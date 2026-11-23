import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsQProjOverCompImmersion
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormMulTransposeMulFormInvMem
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolUnitNeZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsMonHomOfClassifying
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NearIsIsoOfIsProperOfFinitePresentation
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TheoremOfCubeAbelianSchemeOverArbitraryBase
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.MulAFiniteFlatSurjective
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFiniteAndFlatTorsion
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DualAbelianSchemeExistsBiduality
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsDualOfIsPerfectOfAdditive
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LiftLeftFst

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor GlobalTheory.EndLoc
open GlobalTheory.AbDual GlobalTheory.CechPic
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.ZarhinUniqBundle

variable {S : Scheme.{0}} {h M : ℕ} {B : Type} [CommRing B] {ζ : B} {s : S ⟶ Sp B}

theorem evc_symm (o : SiegPre h M ζ s) {Y : Over S} (a b : Y ⟶ o.A) :
    evc o.isLB a b = evc o.isLB b a := by
  have hs : (swap o.P).IsLB := pull_isLB o.isLB _
  have c : cls o.P o.isLB = cls (swap o.P) hs := (cls_eq_iff o.isLB hs).2 o.symm
  rw [← evc_swap o.isLB hs b a]
  simp only [evc, c]

theorem additive (o : SiegPre h M ζ s) : IsAdditive o.P ∧ IsAdditive (swap o.P) :=
  additive_of_cube GlobalTheory.CubeTop.cubeTheorem o.ab o.ab o.isLB o.rig₁ o.rig₂

theorem evc_mul_left (o : SiegPre h M ζ s) {Y : Over S} (a a' b : Y ⟶ o.A) :
    evc o.isLB (a * a') b = evc o.isLB a b + evc o.isLB a' b :=
  (isAdditive_iff o.isLB).1 (additive o).1 Y a a' b

theorem evc_mul_right (o : SiegPre h M ζ s) {Y : Over S} (a b b' : Y ⟶ o.A) :
    evc o.isLB a (b * b') = evc o.isLB a b + evc o.isLB a b' := by
  rw [evc_symm o a, evc_symm o a, evc_symm o a]; exact evc_mul_left o _ _ _

theorem isPerfect (o : SiegPre h M ζ s) (hp : o.Principal) : IsPerfect o.A o.A o.P := by
  refine ⟨o.isLB, o.rig₁, o.rig₂, fun T x hx ↦ hp.2 T x ?_, fun T x hx ↦ hp.2 T x ?_⟩
  · have e := congrArg (pull (lift (snd o.A T) (fst o.A T)).left) ((triv_ev_iff o.isLB _ _).1 hx)
    rw [pull_evc, map_zero, lift_fst_assoc, lift_snd] at e
    exact (triv_ev_iff o.isLB _ _).2 e
  · have e := (triv_ev_iff o.isLB _ _).1 hx
    rw [evc_symm o] at e
    exact (triv_ev_iff o.isLB _ _).2 e

end GlobalTheory.ZarhinUniqBundle

namespace GlobalTheory.ZarhinUniqBundle

open Matrix GlobalTheory.ZarhinFam

def colU (d : ℕ) (k : Fin 4 ⊕ Fin 4) : ord d :=
  ⟨(d : ℤ) • single k (Sum.inl 0) 1, fun i j ↦ by rw [Matrix.smul_apply, smul_eq_mul]; exact dvd_mul_right _ _⟩

def rowU (d : ℕ) (k : Fin 4 ⊕ Fin 4) : ord d :=
  ⟨single (Sum.inl 0) k 1, fun i j ↦ by simp [single]⟩

theorem natCast_eq_sum (d : ℕ) : ((d : ℕ) : ord d) = ∑ k, colU d k * idem d * rowU d k := by
  apply Subtype.ext
  have hs : ((∑ k, colU d k * idem d * rowU d k : ord d) : Matrix (Fin 4 ⊕ Fin 4) (Fin 4 ⊕ Fin 4) ℤ) =
      ∑ k, (colU d k : Matrix _ _ ℤ) * (idem d : Matrix _ _ ℤ) * (rowU d k : Matrix _ _ ℤ) := by
    simp only [AddSubmonoidClass.coe_finset_sum, Subring.coe_mul]
  rw [hs]
  ext i j
  simp only [colU, rowU, idem, Matrix.smul_mul, single_mul_single_same, _root_.mul_one, Matrix.sum_apply,
    Matrix.smul_apply, smul_eq_mul, SubringClass.coe_natCast, Matrix.natCast_apply, single_apply]
  by_cases hij : i = j
  · subst hij; simp
  · have hx : ∀ x : Fin 4 ⊕ Fin 4, ¬ (x = i ∧ x = j) := fun x hx ↦ hij (hx.1.symm.trans hx.2)
    simp [hij, hx]

end GlobalTheory.ZarhinUniqBundle

namespace GlobalTheory.ZarhinUniqBundle

open ReciprocityTheory.ChartRestriction.G.Out in

theorem cancel_pow : ∀ (S : Scheme.{0}) (A B : Over S) [GrpObj A] [GrpObj B], IsAbelianScheme A → ∀ d : ℕ, 0 < d →
    ∀ f g : A ⟶ B, (𝟙 A ^ d) ≫ f = (𝟙 A ^ d) ≫ g → f = g := by
  intro S A B _ _ hA d hd f g hfg
  have hc := hA.comm
  obtain ⟨hfin, hfl⟩ := GlobalTheory.AbTorsionAnyBase.isFinite_and_flat_mulA S A hA d hd
  have gi := GlobalTheory.forall_geometricallyIntegral_of_smooth_of_geometricallyConnected
  have hm := GlobalTheory.AbLaw.MulN.isMonHom_mulA A d
  have hsurj : Surjective (ReciprocityTheory.ChartRestriction.G.Out.mulA A d).left :=
    GlobalTheory.AbLaw.MulN.surjective_of_geomFibres _ fun K _ _ t ↦ by
      letI : GrpObj ((Over.pullback t).obj A) := Functor.grpObjObj
      exact (GlobalTheory.flat_and_surjective_of_isFinite_abelianEnd gi K _ (ReciprocityTheory.ChartRestriction.G.Out.TLinPf.isAb_pullback t A hA) _
        inferInstance
        (MorphismProperty.of_isPullback (P := @IsFinite) (GlobalTheory.AbLaw.MulN.isPullback_baseChange t _) hfin)).2
  exact GlobalTheory.DivisibleHom.cancel_of_flat_surjective (ReciprocityTheory.ChartRestriction.G.Out.mulA A d) hfg

end GlobalTheory.ZarhinUniqBundle

namespace GlobalTheory.ZarhinUniqBundle

theorem isDual_of_isPerfect : ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A], IsAbelianScheme A →
    ∀ (P : LB (A ⊗ A).left), IsPerfect A A P → IsAdditive P → IsAdditive (swap P) → IsDual A A P := by
  intro S A _ hA P hP a₁ a₂
  obtain ⟨D, _, Q, hD', -, q, q'⟩ := GlobalTheory.dualAbelianScheme S A hA
  obtain ⟨x, hx, e⟩ := GlobalTheory.BirigidLift.exists_hom q q'.additive hP.isLB a₁ a₂
  have ix : IsIso x := isIso_of_isIso_pullback hA hD' x fun Ω _ _ s ↦ by
    letI : GrpObj ((Over.pullback s).obj A) := Functor.grpObjObj
    letI : GrpObj ((Over.pullback s).obj D) := Functor.grpObjObj
    have f := isGrpPullback_pullback A s
    have d := isGrpPullback_pullback D s
    have hA₀ := GlobalTheory.PolPull.isAbelianScheme_of_isGrpPullback hA f
    have := hA₀.comm
    obtain ⟨g, hg⟩ := GlobalTheory.AbelianDim.exists_relDim Ω _ hA₀
    obtain ⟨m', m'₁, m'₂⟩ := exists_prod_pullback f f
    have hP₀ := pull_isLB hP.isLB m'
    have p₀ := GlobalTheory.PerfectDual.isDual_of_isPerfect GlobalTheory.dualAbelianScheme _ _ hA₀ hA₀ hg hg
      (hP.baseChange f f m'₁ m'₂ hP₀ ((cls_eq_iff hP₀ hP₀).1 rfl))
    obtain ⟨m, m₁, m₂⟩ := exists_prod_pullback f d
    have hQ := pull_isLB q.isLB m
    have q₀ := q.baseChange f d m₁ m₂ hQ ((cls_eq_iff hQ hQ).1 rfl)
    refine p₀.isIso_of_cls q₀ ?_
    rw [cls_pull hP.isLB _ hP₀, e]
    exact GlobalTheory.BirigidLift.pull_evc_eq m'₁ m'₂ m₁ m₂ q.isLB hQ (x := x) (pullback.lift_fst _ _ _).symm
  exact isDual_of_iso S A A D P Q q hP.isLB x ix hx ((cls_eq_iff hP.isLB (pull_isLB q.isLB _)).1 e)

end GlobalTheory.ZarhinUniqBundle

namespace GlobalTheory.ZarhinUniqBundle

open GlobalTheory.ZarhinFam

section Act

variable {S : Scheme.{0}} {O : Type} [Ring O] {A : Over S} [GrpObj A] [IsCommMonObj A] {act : O → (A ⟶ A)}

theorem act_zero (hr : IsRAct A act) : act 0 = 1 := by
  have e := hr.2.2.2 0 0
  rw [add_zero] at e
  exact (mul_eq_left.1 e.symm)

theorem act_natCast (hr : IsRAct A act) (n : ℕ) : act (n : O) = 𝟙 A ^ n := by
  induction n with
  | zero => rw [Nat.cast_zero, act_zero hr, pow_zero]
  | succ n ih => rw [Nat.cast_succ, hr.2.2.2, ih, hr.2.1, pow_succ]

theorem act_sum (hr : IsRAct A act) {κ : Type} (s : Finset κ) (f : κ → O) :
    act (∑ i ∈ s, f i) = ∏ i ∈ s, act (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => rw [Finset.sum_empty, Finset.prod_empty, act_zero hr]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.prod_insert ha, hr.2.2.2, ih]

end Act

theorem prod_comp {S : Scheme.{0}} {A B : Over S} [GrpObj A] [IsCommMonObj A] [GrpObj B] [IsCommMonObj B]
    {κ : Type} (s : Finset κ) (f : κ → (A ⟶ A)) (u : A ⟶ B) [IsMonHom u] :
    (∏ i ∈ s, f i) ≫ u = ∏ i ∈ s, (f i ≫ u) := by
  classical
  induction s using Finset.induction_on with
  | empty => rw [Finset.prod_empty, Finset.prod_empty, MonObj.one_comp]
  | insert a s ha ih => rw [Finset.prod_insert ha, Finset.prod_insert ha, MonObj.mul_comp, ih]

theorem evc_adj {S : Scheme.{0}} {h M : ℕ} {B : Type} [CommRing B] {ζ : B} {s : S ⟶ Sp B} {O : Type} [Ring O]
    (o : SiegPre h M ζ s) {bar' : O → O} {act : O → (o.A ⟶ o.A)} (ha : Adj o.A o.P bar' act) (a : O)
    {Y : Over S} (x y : Y ⟶ o.A) : evc o.isLB (x ≫ act a) y = evc o.isLB x (y ≫ act (bar' a)) := by
  have h1 := pull_isLB o.isLB (lift (fst o.A o.A ≫ act a) (snd o.A o.A)).left
  have h2 := pull_isLB o.isLB (lift (fst o.A o.A) (snd o.A o.A ≫ act (bar' a))).left
  have c := (cls_eq_iff h1 h2).2 (ha a)
  have k := congrArg (pull (lift x y).left) c
  rw [cls_pull o.isLB _ h1, cls_pull o.isLB _ h2, ← pull_comp, ← pull_comp, ← Over.comp_left, ← Over.comp_left,
    comp_lift, comp_lift, lift_fst_assoc, lift_snd, lift_fst, lift_snd_assoc] at k
  exact k

theorem lbIso_of_ordLinear : ∀ (h M d : ℕ), 0 < d → ∀ (S : Scheme.{0}) (t : S ⟶ Sp (cycAway M)) (c : SiegPre h M (zetaAway M) t) (z₁ z₂ : SiegPre (8 * h) M (zetaAway M) t) (act₁ : GlobalTheory.ZarhinFam.ord d → (z₁.A ⟶ z₁.A)) (act₂ : GlobalTheory.ZarhinFam.ord d → (z₂.A ⟶ z₂.A)) (inc₁ : c.A ⟶ z₁.A) (pr₁ : z₁.A ⟶ c.A) (inc₂ : c.A ⟶ z₂.A) (e : z₁.A ≅ z₂.A), IsUnit ((d : ℕ) : Γ(S, ⊤)) → SiegKerBy c d → z₁.Principal → z₂.Principal → IsRAct z₁.A act₁ → IsRAct z₂.A act₂ → Adj z₁.A z₁.P (GlobalTheory.ZarhinFam.bar d) act₁ → Adj z₂.A z₂.P (GlobalTheory.ZarhinFam.bar d) act₂ → IsMonHom inc₁ → IsMonHom pr₁ → inc₁ ≫ pr₁ = 𝟙 c.A → pr₁ ≫ inc₁ = act₁ (GlobalTheory.ZarhinFam.idem d) → LBIso c.P (z₁.P.pull (inc₁ ⊗ₘ inc₁).left) → LBIso c.P (z₂.P.pull (inc₂ ⊗ₘ inc₂).left) → IsMonHom e.hom → inc₁ ≫ e.hom = inc₂ → (∀ o, act₁ o ≫ e.hom = e.hom ≫ act₂ o) → LBIso z₁.P (z₂.P.pull (e.hom ⊗ₘ e.hom).left) := by
  intro h M d hd S t c z₁ z₂ act₁ act₂ inc₁ pr₁ inc₂ e hdu hker hp₁ hp₂ hr₁ hr₂ ha₁ ha₂ hi hpr hip hpi hc₁ hc₂
    he hinc hact
  have hL₁ := z₁.isLB
  have hL₂ := z₂.isLB
  have hD : IsDual z₁.A z₁.A z₁.P :=
    isDual_of_isPerfect S z₁.A z₁.ab z₁.P (isPerfect z₁ hp₁) (additive z₁).1 (additive z₁).2
  have hP' : (z₂.P.pull (e.hom ⊗ₘ e.hom).left).IsLB := pull_isLB hL₂ _
  have K' : ∀ (Y : Over S) (a b : Y ⟶ z₁.A), evc hP' a b = evc hL₂ (a ≫ e.hom) (b ≫ e.hom) := by
    intro Y a b
    rw [evc, evc, cls_pull hL₂ _ hP', ← pull_comp, ← Over.comp_left, lift_map]
  have hs' : (swap (z₂.P.pull (e.hom ⊗ₘ e.hom).left)).IsLB := pull_isLB hP' _
  have addP' : IsAdditive (z₂.P.pull (e.hom ⊗ₘ e.hom).left) := (isAdditive_iff hP').2 fun Y a a' b ↦ by
    rw [K', K', K', MonObj.mul_comp]; exact evc_mul_left z₂ _ _ _
  have addP's : IsAdditive (swap (z₂.P.pull (e.hom ⊗ₘ e.hom).left)) := (isAdditive_iff hs').2 fun Y b b' a ↦ by
    rw [evc_swap hP' hs', evc_swap hP' hs', evc_swap hP' hs', K', K', K', MonObj.mul_comp]
    exact evc_mul_right z₂ _ _ _
  obtain ⟨u, hu, -⟩ := hD.univ z₁.A _ hP' addP'
  have hE : (ev z₁.P (fst z₁.A z₁.A) (snd z₁.A z₁.A ≫ u)).IsLB := pull_isLB hL₁ _
  have Ku : ∀ (Y : Over S) (a b : Y ⟶ z₁.A), evc hP' a b = evc hL₁ a (b ≫ u) := by
    intro Y a b
    have cc : cls _ hP' = cls _ hE := (cls_eq_iff hP' hE).2 hu
    have k := evc_ev hL₁ (fst z₁.A z₁.A) (snd z₁.A z₁.A ≫ u) hE a b
    rw [lift_fst, lift_snd_assoc] at k
    rw [← k, evc, evc, cc]
  haveI hum : IsMonHom u :=
    isMonHom_of_classifying S z₁.A z₁.A z₁.A _ z₁.P hD (additive z₁).2 hP' addP's u hu
  have adj' : ∀ (a : ord d) (Y : Over S) (x y : Y ⟶ z₁.A),
      evc hP' (x ≫ act₁ a) y = evc hP' x (y ≫ act₁ (bar d a)) := by
    intro a Y x y
    rw [K', K']
    simp only [Category.assoc, hact]
    rw [← Category.assoc x, evc_adj z₂ ha₂, Category.assoc]
  have comm : ∀ N, act₁ N ≫ u = u ≫ act₁ N := by
    intro N
    apply hD.eq_of_evc (T := z₁.A)
    have step : ∀ (Y : Over S) (x y : Y ⟶ z₁.A),
        evc hL₁ x (y ≫ act₁ N ≫ u) = evc hL₁ x (y ≫ u ≫ act₁ N) := by
      intro Y x y
      calc evc hL₁ x (y ≫ act₁ N ≫ u) = evc hP' x (y ≫ act₁ N) := by rw [Ku, Category.assoc]
        _ = evc hP' (x ≫ act₁ (bar d N)) y := by rw [adj', bar_bar hd]
        _ = evc hL₁ (x ≫ act₁ (bar d N)) (y ≫ u) := Ku _ _ _
        _ = evc hL₁ x ((y ≫ u) ≫ act₁ (bar d (bar d N))) := evc_adj z₁ ha₁ _ _ _
        _ = evc hL₁ x (y ≫ u ≫ act₁ N) := by rw [bar_bar hd, Category.assoc]
    exact step _ _ _
  haveI := hi
  haveI := hpr
  haveI := he
  obtain ⟨ψ, hψdef⟩ : ∃ ψ : c.A ⟶ c.A, ψ = inc₁ ≫ u ≫ pr₁ := ⟨_, rfl⟩
  have hincu : inc₁ ≫ u = ψ ≫ inc₁ := by
    calc inc₁ ≫ u = (inc₁ ≫ pr₁ ≫ inc₁) ≫ u := by rw [← Category.assoc inc₁ pr₁, hip, Category.id_comp]
      _ = inc₁ ≫ act₁ (idem d) ≫ u := by rw [← hpi]; simp only [Category.assoc]
      _ = inc₁ ≫ u ≫ act₁ (idem d) := by rw [comm]
      _ = ψ ≫ inc₁ := by rw [← hpi]; simp only [hψdef, Category.assoc]
  have hγ : ∀ (z : SiegPre (8 * h) M (zetaAway M) t) (inc : c.A ⟶ z.A),
      LBIso c.P (z.P.pull (inc ⊗ₘ inc).left) → ∀ (Y : Over S) (a b : Y ⟶ c.A),
      evc c.isLB a b = evc z.isLB (a ≫ inc) (b ≫ inc) := by
    intro z inc hc Y a b
    have h1 := pull_isLB z.isLB (inc ⊗ₘ inc).left
    have cc := (cls_eq_iff c.isLB h1).2 hc
    rw [evc, evc, cc, cls_pull z.isLB _ h1, ← pull_comp, ← Over.comp_left, lift_map]
  have hψ : ∀ (Y : Over S) (a b : Y ⟶ c.A), evc c.isLB a (b ≫ ψ) = evc c.isLB a b := by
    intro Y a b
    rw [hγ z₁ inc₁ hc₁ _ a (b ≫ ψ), hγ z₂ inc₂ hc₂ _ a b, Category.assoc b ψ, ← hincu, ← Category.assoc, ← Ku, K',
      ← hinc]
    simp only [Category.assoc]
  have hw : (ψ * (𝟙 c.A)⁻¹) ^ d = 1 := by
    refine hker.2 c.A _ ((triv_ev_iff c.isLB _ _).2 ?_)
    rw [evc_symm c]
    have e1 := evc_mul_right c (fst c.A c.A) (snd c.A c.A ≫ (ψ * (𝟙 c.A)⁻¹)) (snd c.A c.A)
    have e2 : (snd c.A c.A ≫ (ψ * (𝟙 c.A)⁻¹)) * snd c.A c.A = snd c.A c.A ≫ ψ := by
      conv_rhs => rw [← inv_mul_cancel_right ψ (𝟙 c.A)]
      rw [MonObj.comp_mul (snd c.A c.A) (ψ * (𝟙 c.A)⁻¹) (𝟙 c.A), Category.comp_id]
    rw [e2, hψ] at e1
    exact left_eq_add.1 (e1.trans (add_comm _ _))
  haveI : IsMonHom ψ := by rw [hψdef]; infer_instance
  have hψd : (𝟙 c.A ^ d) ≫ ψ = (𝟙 c.A ^ d) ≫ 𝟙 c.A := by
    rw [MonObj.pow_comp, Category.id_comp, Category.comp_id]
    rw [mul_pow, inv_pow, mul_inv_eq_one] at hw
    exact hw
  have hψ1 : ψ = 𝟙 c.A := cancel_pow S c.A c.A c.ab d hd ψ (𝟙 _) hψd
  have hincu' : inc₁ ≫ u = inc₁ := by rw [hincu, hψ1, Category.id_comp]
  have hsum := act_sum hr₁ Finset.univ (fun k ↦ colU d k * idem d * rowU d k)
  rw [← natCast_eq_sum, act_natCast hr₁] at hsum
  have key : (𝟙 z₁.A ^ d) ≫ u = (𝟙 z₁.A ^ d) ≫ 𝟙 _ := by
    rw [hsum, prod_comp, Category.comp_id]
    refine Finset.prod_congr rfl fun k _ ↦ ?_
    rw [hr₁.2.2.1, hr₁.2.2.1, ← hpi]
    simp only [Category.assoc]
    rw [comm, ← Category.assoc inc₁ u, hincu']
  have hu1 : u = 𝟙 _ := cancel_pow S z₁.A z₁.A z₁.ab d hd u (𝟙 _) key
  have cc : cls _ hP' = cls z₁.P hL₁ := by
    rw [(cls_eq_iff hP' hE).2 hu, cls_pull hL₁ _ hE, hu1, Category.comp_id, lift_fst_snd, Over.id_left, pull_id]
  exact (cls_eq_iff hL₁ hP').1 cc.symm

end GlobalTheory.ZarhinUniqBundle
