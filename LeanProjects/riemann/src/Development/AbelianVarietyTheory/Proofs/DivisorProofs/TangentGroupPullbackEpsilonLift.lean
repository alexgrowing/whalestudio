import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsUniqueIsTanFrameOfIsEmpty
import Development.AbelianVarietyTheory.Definitions.Divisors.P22
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KodairaSpencerMatrixUnique
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPolarizationFormIsotropicFiltration
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsUniqueIsConnOfLift

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry DividedPowers TensorProduct TrivSqZeroExt
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.CrysConn

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.KSSym

variable {R : Type} [CommRing R] {X : Scheme.{0}}

abbrev epsMap {B B' : Type} [CommRing B] [CommRing B'] (σ : B →+* B') : DualNumber B →+* DualNumber B' :=
  extMap σ σ.toSemilinearMap

@[simp] theorem fst_epsMap {B B' : Type} [CommRing B] [CommRing B'] (σ : B →+* B') (a : DualNumber B) :
    (epsMap σ a).fst = σ a.fst := add_zero _

@[simp] theorem snd_epsMap {B B' : Type} [CommRing B] [CommRing B'] (σ : B →+* B') (a : DualNumber B) :
    (epsMap σ a).snd = σ a.snd := zero_add _

theorem isDPMorphism_epsMap {B : Type} [CommRing B] {J : Ideal B} (δ : DividedPowers J) (σ : R →+* B) :
    IsDPMorphism (epsDP R) (extDP B δ) (epsMap σ) := by
  have hm : ∀ a ∈ RingHom.ker (fstHom R R R).toRingHom, (epsMap σ a).fst = 0 := fun a ha ↦ by
    have ha' : a.fst = 0 := ha
    rw [fst_epsMap, ha', map_zero]
  have hJ : ∀ a ∈ RingHom.ker (fstHom R R R).toRingHom, epsMap σ a ∈ J.comap (pr B B) := fun a ha ↦ by
    change (epsMap σ a).fst ∈ J
    rw [hm a ha]; exact J.zero_mem
  refine (isDPMorphism_iff _ _ _).2 ⟨Ideal.map_le_iff_le_comap.2 hJ, fun n hn a ha ↦ ?_⟩
  rcases n with _ | _ | n
  · exact absurd rfl hn
  · rw [zero_add, (epsDP R).dpow_one ha, (extDP B δ).dpow_one (hJ a ha)]
  · have e : (epsDP R).dpow (n + 1 + 1) a = 0 := squareZeroDividedPowers_dpow _ (by omega) a
    rw [e, map_zero]
    refine TrivSqZeroExt.ext ?_ ?_
    · rw [fst_extDP, hm a ha, dpow_eval_zero _ (by omega)]; rfl
    · rw [snd_extDP, hm a ha, dpPred, dpow_eval_zero _ (by omega), zero_smul]; rfl

variable {s : X ⟶ Sp R} {s' : X ⟶ Sp (DualNumber R)}

def epsThick (hs : s' = s ≫ DeRham.epsRed R) (T : Thick (dp0 R) s) : Thick (epsDP R) s' where
  B := DualNumber T.B
  alg := (epsMap (algebraMap R T.B)).toAlgebra
  J := T.J.comap (pr T.B T.B)
  δ := extDP T.B T.δ
  nil := isDPNilpotent_extend _ T.nil
  dp := isDPMorphism_epsMap T.δ _
  B₀ := T.B₀
  π := T.π.comp (pr T.B T.B)
  surj := T.surj.comp fun r ↦ ⟨inl r, rfl⟩
  ker := fun b ↦ T.ker b.fst
  x := T.x
  w := by
    rw [hs, ← Category.assoc, T.w, ← Cris.spMap_comp]
    congr 1
    exact RingHom.ext fun a ↦ congrArg T.π (fst_epsMap (algebraMap R T.B) a).symm

def epsFunctor (hs : s' = s ≫ DeRham.epsRed R) : Thick (dp0 R) s ⥤ Thick (epsDP R) s' where
  obj := epsThick hs
  map {T T'} f :=
    { φ := { epsMap (f.φ : T.B →+* T'.B) with
        commutes' := fun r ↦ TrivSqZeroExt.ext
          ((fst_epsMap _ _).trans ((congrArg _ (fst_epsMap _ _)).trans
            ((f.φ.commutes _).trans (fst_epsMap (algebraMap R T'.B) r).symm)))
          ((snd_epsMap _ _).trans ((congrArg _ (snd_epsMap _ _)).trans
            ((f.φ.commutes _).trans (snd_epsMap (algebraMap R T'.B) r).symm))) }
      φ₀ := f.φ₀
      comm := fun b ↦ (f.comm _).trans (congrArg T'.π (fst_epsMap (f.φ : T.B →+* T'.B) b).symm)
      dp := isDPMorphism_extMap f.dp _
      pt := f.pt }
  map_id T := Thick.hom_ext fun b ↦ TrivSqZeroExt.ext (fst_epsMap _ _) (snd_epsMap _ _)
  map_comp f g := Thick.hom_ext fun b ↦ TrivSqZeroExt.ext
    ((fst_epsMap _ _).trans ((congrArg _ (fst_epsMap _ _)).symm.trans (fst_epsMap _ _).symm))
    ((snd_epsMap _ _).trans ((congrArg _ (snd_epsMap _ _)).symm.trans (snd_epsMap _ _).symm))

def inlCoef (hs : s' = s ≫ DeRham.epsRed R) :
    CoefMap (algebraMap R (DualNumber R)) (O (dp0 R) s) (epsFunctor hs ⋙ O (epsDP R) s') where
  G := 𝟭 _
  α T := algebraMap T.B (DualNumber T.B)
  naturality {T T'} f b := TrivSqZeroExt.ext (fst_epsMap (f.φ : T.B →+* T'.B) (inl b)).symm
    ((map_zero (f.φ : T.B →+* T'.B)).symm.trans (snd_epsMap (f.φ : T.B →+* T'.B) (inl b)).symm)
  smul T r b := by
    have e : ∀ b : T.B, (inl (r • b) : DualNumber T.B) = epsMap (algebraMap R T.B) (inl r) * inl b := fun b ↦ by
      ext <;> simp [Algebra.smul_def]
    exact e b

theorem eq_zero_of_pull2 (hs : s' = s ≫ DeRham.epsRed R) {φ : X ⟶ X} (hφ : φ = 𝟙 X)
    (m : IsMor (dp0 R) s (epsDP R) s' (algebraMap R (DualNumber R)) φ) (z₀ z₁ : SecondDeRham s)
    (h : m.pull2 z₀ + (DualNumber.eps : DualNumber R) • m.pull2 z₁ = 0) : z₀ = 0 ∧ z₁ = 0 := by
  let n := CoefMap.restrict (O (epsDP R) s') (epsFunctor hs)
  let θ : (inlCoef hs).G ⟶ (m.coef.comp n).G :=
    { app := fun T ↦
        { φ := { algebraMap T.B (DualNumber T.B) with
            commutes' := fun r ↦ TrivSqZeroExt.ext (fst_epsMap (algebraMap R T.B) (inl r)).symm
              ((map_zero (algebraMap R T.B)).symm.trans (snd_epsMap (algebraMap R T.B) (inl r)).symm) }
          φ₀ := RingHom.id _
          comm := fun _ ↦ rfl
          dp := isDPMorphism_inl T.B T.δ
          pt := by
            change spMap (RingHom.id T.B₀) ≫ T.x = T.x ≫ φ
            rw [Cris.spMap_id, hφ]; simp }
      naturality := fun T T' f ↦ Thick.hom_ext fun b ↦ (inlCoef hs).naturality f b }
  have key : ∀ z, n.pull2 (m.pull2 z) = (inlCoef hs).pull2 z := fun z ↦
    (m.coef.pullCohomologyTwo_comp n z).symm.trans
      ((inlCoef hs).pullCohomologyTwo_eq_of_natTrans (m.coef.comp n) θ (fun _ _ ↦ rfl) z).symm
  have h1 := congrArg n.pull2 h
  rw [map_add, map_smul, key, key, map_zero] at h1
  obtain ⟨z₀, rfl⟩ := H2.mk_surjective _ z₀
  obtain ⟨z₁, rfl⟩ := H2.mk_surjective _ z₁
  rw [CoefMap.pullCohomologyTwo_class, CoefMap.pullCohomologyTwo_class, ← map_smul, ← map_add, H2.mk_eq_zero] at h1
  obtain ⟨f, hf⟩ := h1
  have alg : ∀ {B B' : Type} [CommRing B] [CommRing B'] (σ : B →+* B') (τ : R →+* B') (u : DualNumber B)
      (v w : DualNumber B') (a b : B'), epsMap σ u - v + w = inl a + epsMap τ DualNumber.eps * inl b →
      σ u.fst - v.fst + w.fst = a ∧ σ u.snd - v.snd + w.snd = b := fun σ τ u v w a b e ↦
    ⟨by simpa using congrArg TrivSqZeroExt.fst e, by simpa using congrArg TrivSqZeroExt.snd e⟩
  have hv := fun (T T' T'' : Thick (dp0 R) s) (a : T ⟶ T') (b : T' ⟶ T'') ↦
    alg (b.φ : T'.B →+* T''.B) (algebraMap R T''.B) (f T T' a) (f T T'' (a ≫ b)) (f T' T'' b) (z₀.1 T T' T'' a b)
      (z₁.1 T T' T'' a b) (congrFun (congrFun (congrFun (congrFun (congrFun hf T) T') T'') a) b)
  constructor
  · refine H2.mk_eq_zero.2 ⟨fun T T' a ↦ TrivSqZeroExt.fst (R := T'.B) (M := T'.B) (f T T' a), ?_⟩
    funext T T' T'' a b
    exact (hv T T' T'' a b).1
  · refine H2.mk_eq_zero.2 ⟨fun T T' a ↦ TrivSqZeroExt.snd (R := T'.B) (M := T'.B) (f T T' a), ?_⟩
    funext T T' T'' a b
    exact (hv T T' T'' a b).2

open GlobalTheory.Published

theorem exists_const_add (P : AbelianDeRham) {A : Over (Sp R)} [GrpObj A] {g : ℕ} (hA : IsAbelianScheme A)
    (hg : SmoothOfRelativeDimension g A.hom) (p : prim (epsDP R) (DeRham.epsRed R) A) :
    ∃ u v : primDR A, p = (constMor A).pull u + (DualNumber.eps : DualNumber R) • (constMor A).pull v := by
  obtain ⟨z, rfl⟩ := constMor_surjective P hA hg p
  induction z with
  | zero => exact ⟨0, 0, by simp only [map_zero, smul_zero, add_zero]⟩
  | add x y hx hy =>
    obtain ⟨u, v, e⟩ := hx
    obtain ⟨u', v', e'⟩ := hy
    refine ⟨u + u', v + v', ?_⟩
    rw [map_add, e, e', map_add, map_add, smul_add]
    abel
  | tmul r c =>
    refine ⟨r.fst • c, r.snd • c, ?_⟩
    rw [liftSemi_tmul, LinearMap.map_smulₛₗ, LinearMap.map_smulₛₗ, smul_smul, ← add_smul]
    congr 1
    ext <;> simp [TrivSqZeroExt.algebraMap_eq_inl]

theorem exists_wedge (P : AbelianDeRham.Free) {A : Over (Sp R)} [GrpObj A] {g : ℕ} (hA : IsAbelianScheme A)
    (hg : SmoothOfRelativeDimension g A.hom) (x y : HdR A) :
    ∃ Λ : SecondDeRham (A.hom ≫ 𝟙 _) →ₗ[R] R, ∀ c d : primDR A, Λ (cup _ c.1 d.1) = x c * y d - x d * y c := by
  obtain ⟨h0, -, -, -, e, he⟩ := P R A g hA hg
  let o : primDR A ≃ₗ[R] FirstDeRham (A.hom ≫ 𝟙 _) := LinearEquiv.ofTop _ h0
  let x' : Module.Dual R (FirstDeRham (A.hom ≫ 𝟙 _)) := x ∘ₗ o.symm.toLinearMap
  let y' : Module.Dual R (FirstDeRham (A.hom ≫ 𝟙 _)) := y ∘ₗ o.symm.toLinearMap
  have ex : ∀ c : primDR A, x' c.1 = x c := fun c => congrArg x (o.symm_apply_apply c)
  have ey : ∀ c : primDR A, y' c.1 = y c := fun c => congrArg y (o.symm_apply_apply c)
  refine ⟨exteriorPower.alternatingMapLinearEquiv (wedgeDual x' y') ∘ₗ e.symm.toLinearMap, fun c d ↦ ?_⟩
  rw [← he, LinearMap.comp_apply, LinearEquiv.coe_coe, e.symm_apply_apply]
  simp [wedgeDual, ex, ey]

set_option maxHeartbeats 1000000 in

theorem snd_polForm (P : AbelianDeRham) {A : Over (Sp R)} [GrpObj A] {n : ℕ} (hA : IsAbelianScheme A)
    (hn : SmoothOfRelativeDimension n A.hom) {A' : Over (Sp (DualNumber R))} [GrpObj A'] {i : A.left ⟶ A'.left}
    (h : IsGrpPullback A A' (DeRham.epsRed R) i) {Y : Scheme.{0}} {L : LB Y} (hL : L.IsLB) {π' : A'.left ⟶ Y}
    {ψ : LinearMap.BilinForm R (HdR A)} (hψ : IsPolForm (dp0 R) (𝟙 _) A (L.pull (i ≫ π')) ψ)
    {ψ' : LinearMap.BilinForm (DualNumber R) (HdR A')} (hψ' : IsPolForm (dp0 _) (𝟙 _) A' (L.pull π') ψ')
    {f g k k' : HdR A} {d d' : Crys (epsDP R) (DeRham.epsRed R) A}
    (ed : ∀ c : primDR A, d ((constMor A).pull c) = inl (f c) + inr (k c))
    (ed' : ∀ c : primDR A, d' ((constMor A).pull c) = inl (g c) + inr (k' c)) :
    (ψ' (crysToDR (epsDP R) h d) (crysToDR (epsDP R) h d')).snd = ψ f k' + ψ k g := by
  obtain ⟨N, a, b, hc, rfl⟩ := hψ
  obtain ⟨N', a', b', hc', rfl⟩ := hψ'
  have c₀ := isChern_pull (constMor A).isMor hc
  have c₁ := isChern_pull (liftMor (epsDP R) h).isMor hc'
  have hl := pull_isLB hL (i ≫ π')
  have iso := (isChern_existsUnique_and_iso _ _ (epsDP R) _ (A.hom ≫ DeRham.epsRed R)).2
  have c₀' := iso _ _ (pull_isLB hl _) (pull_isLB hL (Over.Hom.left (𝟙 A) ≫ i ≫ π'))
    (LBIso.chartPull (Geo.Tor.chartPullPull (L.pull (i ≫ π')) _ _ rfl) (chartPullSame L _ _ _ _ fun _ => rfl)
      (ChernExists.lbIso_refl hl)) _ c₀
  have c₁' := iso _ _ (pull_isLB (pull_isLB hL π') i) hl
    (LBIso.chartPull (Geo.Tor.chartPullPull (L.pull π') i i rfl) (chartPullSame L _ _ _ i fun _ => rfl)
      (ChernExists.lbIso_refl (pull_isLB hL π'))) _ c₁
  rw [show Over.Hom.left (𝟙 A) ≫ i ≫ π' = i ≫ π' from Category.id_comp _] at c₀'
  have hz := ((isChern_existsUnique_and_iso _ _ (epsDP R) _ _).1 _ hl).unique c₁' c₀'
  choose u v huv using fun j ↦ exists_const_add P hA hn ((liftMor (epsDP R) h).pull (a' j))
  choose w x hwx using fun j ↦ exists_const_add P hA hn ((liftMor (epsDP R) h).pull (b' j))
  have hz' : (constMor A).isMor.pull2 (∑ j, cup _ (u j).1 (w j).1 - ∑ j, cup _ (a j).1 (b j).1) +
      (DualNumber.eps : DualNumber R) •
        (constMor A).isMor.pull2 (∑ j, (cup _ (u j).1 (x j).1 + cup _ (v j).1 (w j).1)) = 0 := by
    rw [map_sub, ← hz, sub_add_eq_add_sub, sub_eq_zero, map_sum, map_sum, map_sum, Finset.smul_sum,
      ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    have e₁ : (liftMor (epsDP R) h).isMor.pull1 (a' j).1 = (constMor A).isMor.pull1 (u j).1 +
      (DualNumber.eps : DualNumber R) • (constMor A).isMor.pull1 (v j).1 := congrArg Subtype.val (huv j)
    have e₂ : (liftMor (epsDP R) h).isMor.pull1 (b' j).1 = (constMor A).isMor.pull1 (w j).1 +
      (DualNumber.eps : DualNumber R) • (constMor A).isMor.pull1 (x j).1 := congrArg Subtype.val (hwx j)
    simp only [map_add, IsMor.pullCohomologyTwo_cup, e₁, e₂,
      map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_add, smul_smul, DualNumber.eps_mul_eps, zero_smul,
      add_zero]
    abel
  obtain ⟨z₀, z₁⟩ := eq_zero_of_pull2 (s := A.hom ≫ 𝟙 _) (by rw [Category.comp_id]) rfl (constMor A).isMor _ _ hz'
  obtain ⟨Λ₁, e₁⟩ := exists_wedge P.1 hA hn f k'
  obtain ⟨Λ₂, e₂⟩ := exists_wedge P.1 hA hn k g
  obtain ⟨Λ₃, e₃⟩ := exists_wedge P.1 hA hn f g
  have t₁ := congrArg Λ₁ (sub_eq_zero.1 z₀)
  have t₂ := congrArg Λ₂ (sub_eq_zero.1 z₀)
  have t₃ := congrArg Λ₃ z₁
  simp only [map_sum, map_add, map_zero, e₁, e₂, e₃] at t₁ t₂ t₃
  rw [wedgeForm_apply, wedgeForm_apply, wedgeForm_apply, ← t₁, ← t₂, ← add_zero (_ + _ : R), ← t₃,
    ← Finset.sum_add_distrib, ← Finset.sum_add_distrib, snd_sum]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  simp only [crysToDR_apply, huv, hwx, map_add, map_smul, ed, ed', smul_eq_mul]
  simp
  ring

end GlobalTheory.KSSym

namespace GlobalTheory.KSSym

open NumberField Formalism.L2.Pj MonObj

theorem ks_symm : GlobalTheory.CovTop.Hypotheses₂ → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E)
    (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (K : Type) [Field K] (x : Sp K ⟶ Xo.X)
    (x' : Sp (DualNumber K) ⟶ Xo.X) (A : Over (Sp K)) [GrpObj A] (A' : Over (Sp (DualNumber K))) [GrpObj A']
    (π : A.left ⟶ Xo.univ.t.G.left) (π' : A'.left ⟶ Xo.univ.t.G.left) (i : A.left ⟶ A'.left)
    (h : IsGrpPullback A A' (GlobalTheory.DeRham.epsRed K) i) (ψ : LinearMap.BilinForm K (GlobalTheory.DeRham.HdR A)),
    IsGrpPullback A Xo.univ.t.G x π → IsGrpPullback A' Xo.univ.t.G x' π' → i ≫ π' = π →
    GlobalTheory.DeRham.IsPolForm (GlobalTheory.Cris.dp0 K) (𝟙 _) A (Xo.univ.t.PP.L.pull π) ψ →
    ∀ f g k k' : GlobalTheory.DeRham.HdR A, GlobalTheory.DeRham.IsFilLift h f k → GlobalTheory.DeRham.IsFilLift h g k' →
      ψ f k' + ψ k g = 0 := by
  rintro Pr E _ _ _ H Dw l Xo K _ x x' A _ A' _ π π' i h ψ hπ hπ' rfl hψ f g k k' ⟨d, hd, ed⟩ ⟨d', hd', ed'⟩
  have hA := PolPull.isAbelianScheme_of_isGrpPullback (ObjDim.isAbelianScheme Xo.univ) hπ
  have gA := (smoothOfRelativeDimension_isStableUnderBaseChange _).of_isPullback hπ.1
    (ObjDim.smoothOfRelativeDimension Xo.univ)
  obtain ⟨ψ', hψ', iso, -⟩ := GlobalTheory.PolExistsRing.polForm_exists Pr.p5 Xo hπ'
  rw [← snd_polForm Pr.p5 hA gA h Xo.univ.t.PP.isLB hψ hψ' ed ed', iso _ hd _ hd']
  rfl

end GlobalTheory.KSSym
