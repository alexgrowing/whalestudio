import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsLatFamilyCongr
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsLieModel
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieModelBaseChangeMapStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieModelFiniteBaseChangeStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeTateFunctionalUniqueStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeTateFunctionalBaseChangeStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.QuasiFiniteGroupFiniteStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.TorsionAlongBaseChangeStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.TorsionAlongUniqueUpToIso
import Development.WeilBound.CoreStatements.HomogeneousNonvanishing.BtExistsBc
import Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.SameGenericPointCharts
open AlgebraicGeometry CategoryTheory NumberField MvPolynomial ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Num GlobalTheory.CompanionTheory.Ar.Top
open GroundTheory.Heights₂.Heights.NumbersDVR (pointIdeal segreVec IsFlagFrame IsFlagPair SameGenericFibre IsModelOver divCycle)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg fnField)
open Limits MonoidalCategory CartesianMonoidalCategory MonObj
open GlobalTheory.CompanionTheory.Ar.Num.FamEx GlobalTheory.CompanionTheory.Ar.BT

namespace PositivityTheory.Xgn.SequenceFamilyOverlap

theorem dualMap_comp {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (c : A →+* B) (d : B →+* C) :
    (dualMap d).comp (dualMap c) = dualMap (d.comp c) := by
  ext r <;> simp [dualMap]

theorem lieBC {S : Scheme.{0}} {G : Over S} [GrpObj G] {A B : Type} [CommRing A] [CommRing B] (c : A →+* B)
    (x : Sp A ⟶ S) (y : Sp B ⟶ S) (hy : y = Spec.map (CommRingCat.ofHom c) ≫ x) (hsm : Smooth G.hom)
    {E E' : Type} [AddCommGroup E] [Module A E] [AddCommGroup E'] [Module B E']
    (M : LieModel G x E) (M' : LieModel G y E') :
    ∃ j : E →+ E', (∀ e, (M'.pt (j e)).left = Spec.map (CommRingCat.ofHom (dualMap c)) ≫ (M.pt e).left) ∧
      (∀ (a : A) e, j (a • e) = c a • j e) ∧ Submodule.span B (Set.range j) = ⊤ ∧
      ∀ l : Module.Dual A E, ∃ l' : Module.Dual B E', ∀ e, l' (j e) = c (l e) := by
  subst hy
  letI : Algebra A B := c.toAlgebra
  letI : Module A E' := Module.compHom E' c
  haveI : IsScalarTower A B E' := ⟨fun a b e => by
    show (c a * b) • e = c a • b • e
    rw [mul_smul]⟩
  haveI : Smooth G.hom := hsm
  obtain ⟨j, h1, h2, -⟩ := GlobalTheory.T.lie_model_base_change_map S G A B x E E' M M'
  let β : E →ₗ[A] E' := { toFun := j, map_add' := map_add j, map_smul' := fun a e => h2 a e }
  have hbc : IsBaseChange B β := (GlobalTheory.T.lie_model_finite_base_change S G A x E M).2.2 B E' M' β h1
  refine ⟨j, h1, h2, ?_, ?_⟩
  · refine eq_top_iff.2 fun e _ => ?_
    refine hbc.inductionOn e (fun z => z ∈ Submodule.span B (Set.range j)) (Submodule.zero_mem _) ?_ ?_ ?_
    · exact fun m => Submodule.subset_span ⟨m, rfl⟩
    · exact fun s n h => Submodule.smul_mem _ s h
    · exact fun a b ha hb => Submodule.add_mem _ ha hb
  · intro l
    refine ⟨hbc.lift ((Algebra.linearMap A B).comp l), fun e => ?_⟩
    exact hbc.lift_eq _ e

theorem isHT_transfer {R : Type} [CommRing R] [IsDomain R] {T : Type} [CommGroup T] {Γ₁ Γ₂ : QFGroup R T}
    {S : Scheme.{0}} {G : Over S} [GrpObj G] {x : Sp R ⟶ S} {N : ℕ} {i₁ : Γ₁.G.left ⟶ G.left}
    {i₂ : Γ₂.G.left ⟶ G.left} (h₁ : Γ₁.IsTorsionAlong G x N i₁) (h₂ : Γ₂.IsTorsionAlong G x N i₂)
    (hp : ∀ t t', (Γ₂.pt t).left ≫ i₂ = (Γ₁.pt t').left ≫ i₁ → t' = t)
    {L : Type} [AddCommGroup L] [Module R L] {M : LieModel G x L} {χ : T →* Rˣ} {w : Module.Dual R L}
    (H : Γ₁.IsHT i₁ M N χ w) : Γ₂.IsHT i₂ M N χ w := by
  obtain ⟨ψ, hψ⟩ := TorIso.exists_hom h₁ h₂
  obtain ⟨ψ', hψ'⟩ := TorIso.exists_hom h₂ h₁
  have c₁ : ψ ≫ ψ' = 𝟙 _ := h₁.inj _ _ _ (by simp [hψ, hψ'])
  have hf' : ∀ t, (Γ₂.pt t).left ≫ ψ'.left = (Γ₁.pt t).left := fun t => by
    obtain ⟨t', ht'⟩ := TorIso.exists_pt (Γ₁ := Γ₂) (Γ₂ := Γ₁) ψ' t
    have e₁ : (Γ₂.pt t).left ≫ ψ'.left = (Γ₁.pt t').left := congrArg (fun z => z.left) ht'
    have := hp t t' (by rw [← e₁, Category.assoc, hψ'])
    rw [e₁, this]
  obtain ⟨s, hs, hv⟩ := H
  refine ⟨ψ'.left.appTop s, fun t => ?_, fun e => ?_⟩
  · refine (TorIso.valAt_comp _ _ s).symm.trans ?_
    rw [hf']
    exact hs t
  · obtain ⟨v, v₁, v₂, v₃⟩ := hv e
    have e₁ : ψ.left ≫ ψ'.left = 𝟙 _ := congrArg (fun z => z.left) c₁
    refine ⟨v ≫ ψ.left, ?_, ?_, ?_⟩
    · rw [Category.assoc, Over.w ψ, v₁]
    · rw [Category.assoc, hψ, v₂]
    · refine (TorIso.valAt_comp _ _ s).symm.trans ?_
      rw [Category.assoc, e₁, Category.comp_id]
      exact v₃

theorem pts_bc {R B Ω : Type} [CommRing R] [IsDomain R] [CommRing B] [IsDomain B] [Field Ω] {T : Type} [CommGroup T]
    {Γ : QFGroup R T} {Γ' : QFGroup B T} {φ : R →+* B} {F : Γ'.G.left ⟶ Γ.G.left} (hF : Γ'.IsBaseChange Γ φ F)
    (a : FractionRing R →+* Ω) (a' : FractionRing B →+* Ω)
    (h : ∀ r, a (algebraMap R _ r) = a' (algebraMap B _ (φ r))) (t : T) :
    spMap a ≫ (Γ.pt t).left = spMap a' ≫ (Γ'.pt t).left ≫ F := by
  obtain ⟨C, _, i, j, j', σ, hj, h1, h2, -, h3, h4⟩ := hF.pts
  have key : a.comp j = a'.comp j' := by
    ext b
    obtain ⟨r, s, hs, e⟩ := IsFractionRing.div_surjective (A := R) (j b)
    have hs0 : algebraMap R (FractionRing R) s ≠ 0 := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hs
    have g1 : ∀ z, j (i z) = algebraMap R _ z := fun z => RingHom.congr_fun h1 z
    have g2 : ∀ z, j' (i z) = algebraMap B _ (φ z) := fun z => RingHom.congr_fun h2 z
    have e1 : b * i s = i r := hj (by rw [map_mul, g1, g1, ← e, div_mul_cancel₀ _ hs0])
    have e2 := congrArg (fun z => a (j z)) e1
    have e3 := congrArg (fun z => a' (j' z)) e1
    simp only [map_mul, g1, g2, ← h] at e2 e3
    exact mul_right_cancel₀ ((map_ne_zero a).2 hs0) (e2.trans e3.symm)
  rw [← h3, ← h4, ← Category.assoc, ← Category.assoc, ← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
    ← CommRingCat.ofHom_comp, key]

theorem step {R B Ω : Type} [CommRing R] [IsDomain R] [CommRing B] [IsDomain B] [Field Ω] (φ : R →+* B)
    (hφ : Function.Injective φ) (k : R →+* Ω) (k' : B →+* Ω) (hk : ∀ r, k' (φ r) = k r)
    (a : FractionRing R →+* Ω) (a' : FractionRing B →+* Ω) (ha : ∀ r, a (algebraMap R _ r) = k r)
    (ha' : ∀ r, a' (algebraMap B _ r) = k' r)
    {X : Scheme.{0}} {G : Over X} [GrpObj G] [IsCommMonObj G] (hsm : Smooth G.hom) (x : Sp R ⟶ X) (x' : Sp B ⟶ X)
    (hx : x' = spMap φ ≫ x) {ξ : Sp Ω ⟶ X} {T : Type} [CommGroup T] (Γ : QFGroup R T) (N : ℕ)
    (i : Γ.G.left ⟶ G.left) (hi : Γ.IsTorsionAlong G x N i)
    {L L' Li : Type} [AddCommGroup L] [Module R L] [AddCommGroup L'] [Module B L'] [AddCommGroup Li] [Module Ω Li]
    (M : LieModel G x L) (M' : LieModel G x' L') (M₀ : LieModel G ξ Li) (tl : L → Li)
    (htl : ∀ v, (M₀.pt (tl v)).left = spMap (dualMap k) ≫ (M.pt v).left) (jj : L' →+ Li)
    (hjj : ∀ v, (M₀.pt (jj v)).left = spMap (dualMap k') ≫ (M'.pt v).left)
    (hjs : ∀ (b : B) e, jj (b • e) = k' b • jj e) :
    (∀ l, tl l ∈ Set.range jj) ∧
    ∃ (Γ' : QFGroup B T) (i' : Γ'.G.left ⟶ G.left), Γ'.IsTorsionAlong G x' N i' ∧
      (∀ t, spMap a ≫ (Γ.pt t).left ≫ i = spMap a' ≫ (Γ'.pt t).left ≫ i') ∧
      ∀ (χ : T →* Rˣ) (w : Module.Dual R L) (W : Module.Dual Ω Li), (∀ l, W (tl l) = k (w l)) →
        Γ.IsHT i M N χ w → ∃ w' : Module.Dual B L', (∀ e, W (jj e) = k' (w' e)) ∧
          Γ'.IsHT i' M' N ((Units.map (φ : R →* B)).comp χ) w' := by
  subst hx
  haveI := GlobalTheory.T.quasi_finite_group_finite R T Γ
  letI : Algebra R B := φ.toAlgebra
  obtain ⟨Γ', F, hF⟩ := PositivityTheory.UnitarySelfGeneration.bt_exists_bc R T Γ B φ hφ
  have tor := GlobalTheory.T.torsion_along_base_change R T Γ X G x N i hi B φ Γ' F hF
  obtain ⟨β, hβ, -, hsp, hext⟩ := lieBC φ x _ rfl hsm M M'
  have hc : ∀ l, jj (β l) = tl l := fun l => M₀.inj (Over.OverMorphism.ext (by
    have e : k'.comp φ = k := RingHom.ext hk
    rw [hjj, htl, hβ, ← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp, dualMap_comp, e]))
  refine ⟨fun l => ⟨_, hc l⟩, Γ', F ≫ i, tor, fun t => ?_, fun χ w W hW H => ?_⟩
  · have := pts_bc hF a a' (fun r => by rw [ha, ha', hk]) t
    rw [← Category.assoc, this]
    simp only [Category.assoc]
  · obtain ⟨w', hw'⟩ := hext w
    refine ⟨w', fun e => ?_, GlobalTheory.T.hodge_tate_functional_base_change R T Γ X G x N i hi L M B Γ' F hF tor L' M' β hβ hsp χ w w' hw' H⟩
    have he : e ∈ Submodule.span B (Set.range β) := by rw [hsp]; trivial
    induction he using Submodule.span_induction with
    | mem _ h =>
      obtain ⟨l, rfl⟩ := h
      rw [hc, hW, hw', hk]
    | zero => simp
    | add a b _ _ ha hb => simp [ha, hb]
    | smul a b _ hb => simp [hjs, hb]

def awaySub {O Ω : Type} [CommRing O] [Field Ω] [Algebra O Ω] (R : Subalgebra O Ω) (f : Ω) (hf : f ∈ R) :
    Subalgebra O Ω where
  carrier := {z | ∃ n : ℕ, f ^ n * z ∈ R}
  mul_mem' := by
    rintro a b ⟨n, hn⟩ ⟨m, hm⟩
    refine ⟨n + m, ?_⟩
    have := mul_mem hn hm
    convert this using 1
    ring
  add_mem' := by
    rintro a b ⟨n, hn⟩ ⟨m, hm⟩
    refine ⟨n + m, ?_⟩
    have := add_mem (mul_mem (pow_mem hf m) hn) (mul_mem (pow_mem hf n) hm)
    convert this using 1
    ring
  algebraMap_mem' r := ⟨0, by simpa using R.algebraMap_mem r⟩

theorem clear {O Ω : Type} [CommRing O] [Field Ω] [Algebra O Ω] (R : Subalgebra O Ω) (f : Ω) (hf : f ∈ R)
    {L : Type} [AddCommGroup L] [Module R L] [Module.Finite R L] (u : L →ₗ[R] Ω)
    (hu : ∀ l, ∃ n : ℕ, f ^ n * u l ∈ R) : ∃ (n : ℕ) (w : Module.Dual R L), ∀ l, ((w l : R) : Ω) = f ^ n * u l := by
  obtain ⟨s, hs⟩ := Module.Finite.fg_top (R := R) (M := L)
  choose g hg using hu
  have key : ∀ l, f ^ (s.sup g) * u l ∈ R := fun l => by
    have hl : l ∈ Submodule.span R (s : Set L) := by rw [hs]; trivial
    induction hl using Submodule.span_induction with
    | mem l h =>
      obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le (Finset.le_sup (f := g) h)
      rw [hd, add_comm, pow_add, _root_.mul_assoc]
      exact mul_mem (pow_mem hf d) (hg l)
    | zero => simp
    | add a b _ _ ha hb => rw [map_add, mul_add]; exact add_mem ha hb
    | smul r b _ hb =>
      rw [map_smul, Algebra.smul_def, mul_left_comm]
      exact mul_mem r.2 hb
  refine ⟨s.sup g,
    { toFun := fun l => ⟨_, key l⟩
      map_add' := fun a b => Subtype.ext (by simp [mul_add])
      map_smul' := fun r b => Subtype.ext ?_ }, fun l => rfl⟩
  show f ^ (s.sup g) * u (r • b) = (r : Ω) * (f ^ (s.sup g) * u b)
  rw [map_smul, Algebra.smul_def, mul_left_comm]
  rfl

end PositivityTheory.Xgn.SequenceFamilyOverlap

open PositivityTheory.Xgn.SequenceFamilyOverlap in
theorem PositivityTheory.Xgn.sequence_family_overlap : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O₀ : Type) [CommRing O₀] (β : O₀ →+* c.F) (Y : Model Xo c β) (S : Finset ℕ) (Ω : Type) [Field Ω] (K : Type) [Fintype K] [DecidableEq K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y) (d : ℕ), IsArithVar (mCoordIdeal y) (d + 1) → 0 < D.p + D.q → ∀ (p : ℕ) [Fact p.Prime], p ∈ S → ∀ (A : Type) [CommRing A] [Algebra A Ω] [IsIntegralClosure A ℤ Ω] (m : Ideal A) [m.IsPrime], (p : A) ∈ m → ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Algebra A O] [IsLocalization.AtPrime O m] [Algebra O Ω] [IsScalarTower A O Ω], ∀ (G : GenTors 𝔐 p) (c₁ c₂ : ∀ k, J k), mseg y c₁ ≠ 0 → mseg y c₂ ≠ 0 → ∀ (P₁ : ChartPack G O c₁) (P₂ : ChartPack G O c₂) (x : Fin (D.p + D.q) → 𝓞 E), ∃ n : ℕ, ∃ u ∈ P₂.Dh.om, (mseg y c₁ / mseg y c₂) ^ n • (P₁.Dh.h x - P₂.Dh.h x) = (p ^ 𝔐.R p) • u := by
  intro E _ _ _ H D l Xo c O₀ _ β Y S Ω _ K _ _ J _ y 𝔐 d hV _ p hp hpS A _ _ _ m _ hpm O _ _ _ _ _ _ _ G c₁ c₂
    hc₁ hc₂ P₁ P₂ x
  haveI : CharZero Ω := (RingHom.charZero_iff 𝔐.cst.injective).1 inferInstance
  have hsm : Smooth 𝔐.t.G.hom := 𝔐.t.semi.smooth
  haveI := 𝔐.t.semi.comm
  haveI := P₂.fin
  have hgen : ∀ c' j, mseg y j / mseg y c' ∈ CR O y c' := fun c' j => Algebra.subset_adjoin ⟨j, rfl⟩
  let B : Subalgebra O Ω := awaySub (CR O y c₂) (mseg y c₁ / mseg y c₂) (hgen c₂ c₁)
  have h₂ : CR O y c₂ ≤ B := fun z hz => ⟨0, by simpa using hz⟩
  have h₁ : CR O y c₁ ≤ B := Algebra.adjoin_le (by
    rintro _ ⟨j, rfl⟩
    refine ⟨1, ?_⟩
    have := hgen c₂ j
    convert this using 1
    field_simp)
  let φ₁ : CR O y c₁ →+* B := (Subalgebra.inclusion h₁).toRingHom
  let φ₂ : CR O y c₂ →+* B := (Subalgebra.inclusion h₂).toRingHom
  have hk₁ : ∀ r, algebraMap B Ω (φ₁ r) = algebraMap (CR O y c₁) Ω r := fun _ => rfl
  have hk₂ : ∀ r, algebraMap B Ω (φ₂ r) = algebraMap (CR O y c₂) Ω r := fun _ => rfl
  have hB : Function.Injective (algebraMap B Ω) := Subtype.val_injective
  have g₁ : spMap (algebraMap B Ω) ≫ spMap φ₁ ≫ P₁.x = 𝔐.ξ := by
    rw [← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    exact P₁.x_gen
  have g₂ : spMap (algebraMap B Ω) ≫ spMap φ₂ ≫ P₂.x = 𝔐.ξ := by
    rw [← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    exact P₂.x_gen
  have hx : spMap φ₂ ≫ P₂.x = spMap φ₁ ≫ P₁.x :=
    PositivityTheory.Xgn.same_generic_point_charts 𝔐.X Ω 𝔐.ξ _ (mseg y) 𝔐.tie c₂ hc₂ B hB
      (fun c' => ⟨⟨_, h₂ (hgen c₂ c')⟩, rfl⟩) _ _ g₂ g₁
  obtain ⟨L', _, _, ⟨M'⟩⟩ := lieModel_exists 𝔐.X 𝔐.t.G B (spMap φ₂ ≫ P₂.x)
  obtain ⟨jj, hjj, hjs, hjsp, hjext⟩ := lieBC (algebraMap B Ω) _ 𝔐.ξ g₂.symm hsm M' 𝔐.M
  have hfr : ∀ (R : Subalgebra O Ω) (r : R), fracToField R (algebraMap R _ r) = algebraMap R Ω r := fun R r =>
    IsFractionRing.lift_algebraMap _ r
  obtain ⟨-, Γ₁, i₁, t₁, q₁, s₁⟩ := step φ₁ (Subalgebra.inclusion_injective h₁) _ _ hk₁ (fracToField _) (fracToField B)
    (hfr _) (hfr _) hsm P₁.x _ hx P₁.Γ₂ _ P₁.i₂ P₁.tors₂ P₁.M M' 𝔐.M P₁.toLi P₁.toLi_pt jj hjj hjs
  obtain ⟨hr, Γ₂, i₂, t₂, q₂, s₂⟩ := step φ₂ (Subalgebra.inclusion_injective h₂) _ _ hk₂ (fracToField _) (fracToField B)
    (hfr _) (hfr _) hsm P₂.x _ rfl P₂.Γ₂ _ P₂.i₂ P₂.tors₂ P₂.M M' 𝔐.M P₂.toLi P₂.toLi_pt jj hjj hjs
  obtain ⟨χ₁, w₁, hχ₁, hh₁, H₁⟩ := P₁.isHT.2.2 x
  obtain ⟨χ₂, w₂, hχ₂, hh₂, H₂⟩ := P₂.isHT.2.2 x
  obtain ⟨w₁', e₁, H₁'⟩ := s₁ χ₁ w₁ (P₁.j w₁) (P₁.j_apply w₁) H₁
  obtain ⟨w₂', e₂, H₂'⟩ := s₂ χ₂ w₂ (P₂.j w₂) (P₂.j_apply w₂) H₂
  have H₁'' := isHT_transfer t₁ t₂ (fun t t' h => G.t₂.inj (Over.OverMorphism.ext (by
    rw [P₁.pts₂ t', P₂.pts₂ t, q₁, q₂, h]))) H₁'
  have hχ : (Units.map (φ₁ : CR O y c₁ →* B)).comp χ₁ = (Units.map (φ₂ : CR O y c₂ →* B)).comp χ₂ := by
    refine MonoidHom.ext fun s => ?_
    choose v hv using fun j => Ideal.Quotient.mk_surjective (Multiplicative.toAdd s j)
    have hs : qhom _ _ (Multiplicative.ofAdd v) = s := congrArg Multiplicative.ofAdd (funext hv)
    subst hs
    refine Units.ext (Subtype.ext ?_)
    show (((χ₁ _ : (CR O y c₁)ˣ) : CR O y c₁) : Ω) = (((χ₂ _ : (CR O y c₂)ˣ) : CR O y c₂) : Ω)
    rw [hχ₁, hχ₂, P₁.Dh_e, P₂.Dh_e, Units.val_pow_eq_pow_val, Units.val_pow_eq_pow_val, SubmonoidClass.coe_pow,
      SubmonoidClass.coe_pow, P₁.ζ_eq, P₂.ζ_eq]
  rw [hχ] at H₁''
  have hN : ((p ^ 𝔐.R p : ℕ) : B) ≠ 0 := fun e => by
    have e' := congrArg (algebraMap B Ω) e
    rw [map_natCast, map_zero] at e'
    exact (Nat.cast_ne_zero.2 (pow_ne_zero _ hp.out.ne_zero)) e'
  haveI := GlobalTheory.T.quasi_finite_group_finite B _ Γ₂
  obtain ⟨u', hu'⟩ := (GlobalTheory.T.hodge_tate_functional_unique_mod_smul B _ Γ₂ 𝔐.X 𝔐.t.G _ _ i₂ t₂ hsm hN L' M' _ w₂' w₁' H₂').1 H₁''
  obtain ⟨U, hU⟩ := hjext u'
  have hdiff : P₁.Dh.h x - P₂.Dh.h x = (p ^ 𝔐.R p) • U := by
    rw [hh₁, hh₂]
    refine LinearMap.ext_on hjsp ?_
    rintro _ ⟨e, rfl⟩
    rw [LinearMap.sub_apply, LinearMap.smul_apply, e₁, e₂, hU, hu', LinearMap.add_apply, LinearMap.smul_apply,
      map_add, map_nsmul, add_sub_cancel_left]
  obtain ⟨n, w₀, hw₀⟩ := clear (CR O y c₂) _ (hgen c₂ c₁) (U.restrictScalars (CR O y c₂) ∘ₗ P₂.toLi) (fun l => by
    obtain ⟨e, he⟩ := hr l
    show ∃ n : ℕ, _ * U (P₂.toLi l) ∈ _
    rw [← he, hU]
    exact (u' e).2)
  have hj : P₂.j w₀ = (mseg y c₁ / mseg y c₂) ^ n • U := P₂.toLi_bc.algHom_ext _ _ fun b => by
    rw [P₂.j_apply]
    exact hw₀ b
  refine ⟨n, P₂.j w₀, by rw [P₂.isHT.1]; exact ⟨w₀, rfl⟩, ?_⟩
  rw [hdiff, hj, smul_comm]
