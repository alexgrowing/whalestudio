import Mathlib
import Development.AutomorphicArithmetic.DivisorFrames.ExistsValuationSubringBelow
import Development.AutomorphicArithmetic.LocalEmbeddings.ConsAgree
import Development.AutomorphicArithmetic.LocalEmbeddings.ConsMatch
import Development.AbelianVarietyTheory.PublishedTheorems.SemiabelianTori.GeometricallyConnectedSplitTorusAff
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsChartOfMaximal
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.GrNormPosOfBasis
open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.LocM GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.ConsGeo

section SlopeTestRemainingChoices
open Formalism.MainNotions.DIV.Cons (intO SCF)
open GlobalTheory.FieldPtGlue GlobalTheory.ShFam.Pad.Pull

private theorem UpperTheory.spMap_comp_spMap_divisor_frames {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap g ≫ spMap f = spMap (g.comp f) := (Spec.map_comp _ _).symm

private theorem UpperTheory.spMap_dualMap_comp_eq_spMap_dualMap_ringHom_comp {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap (dualMap g) ≫ spMap (dualMap f) = spMap (dualMap (g.comp f)) := by
  rw [UpperTheory.spMap_comp_spMap_divisor_frames]
  congr 1
  refine RingHom.ext fun z => ?_
  ext <;> simp [dualMap]

private theorem UpperTheory.spherical_completion_integral {p : ℕ} (hp : p.Prime) {B K : Type} [CommRing B] [IsNoetherianRing B] [Field K]
    [CharZero K] [Countable K] [Algebra B K] [Algebra.EssFiniteType B K] (A : ValuationSubring K)
    (hB : ∀ r, algebraMap B K r ∈ A) (hpA : (p : K) ∈ A.nonunits) {s : Set K} (hs : s.Finite) (hsA : ∀ x ∈ s, x ∈ A)
    {κ : K} (h : ∀ (C : SCF p) (ψ : B →+* ↥(intO ↥C.S)) (θ : K →+* ↥C.S),
      θ.comp (algebraMap B K) = (intO ↥C.S).subtype.comp ψ → (∀ x ∈ s, ‖θ x‖ ≤ 1) → ‖θ κ‖ ≤ 1) : κ ∈ A := by
  by_contra hn
  have h0 : κ ≠ 0 := fun e => hn (e ▸ A.zero_mem)
  have hκ : κ⁻¹ ∈ A.nonunits := A.inv_mem_nonunits_iff.2 (Or.inr hn)
  obtain ⟨V, hV, h₁, h₂, h₄⟩ := exists_discreteValuationSubring_of_valuationSubring (R := B) A hB
    (t := {(p : K), κ⁻¹}) hs (Set.toFinite _) hsA (by rintro x (rfl | rfl) <;> assumption)
    ⟨κ⁻¹, by simp, inv_ne_zero h0⟩
  have hκV : κ ∉ V := (V.inv_mem_nonunits_iff.1 (h₄ _ (by simp))).resolve_left h0
  have hpV : (p : V) ∈ maximalIdeal V := by
    rw [← ValuationSubring.coe_mem_nonunits_iff]
    simpa using h₄ p (by simp)
  obtain ⟨C, φ, φi, hφ⟩ := exists_scf_embedding_dvd p V hp hpV
    ((Cardinal.mk_subtype_le _).trans (Cardinal.mk_le_aleph0.trans Cardinal.aleph0_le_continuum))
  let θ : K →+* ↥C.S := IsFractionRing.lift (A := V) (g := (intO ↥C.S).subtype.comp φ)
    ((intO ↥C.S).subtype_injective.comp φi)
  have hθ (v : V) : θ v = φ v := IsFractionRing.lift_algebraMap _ v
  have h₃ := h C (φ.comp ((algebraMap B K).codRestrict V h₁)) θ (RingHom.ext fun r => hθ ⟨_, h₁ r⟩)
    (fun x hx => by rw [hθ ⟨x, h₂ x hx⟩]; exact (φ _).2)
  have hi : κ⁻¹ ∈ V := (V.mem_or_inv_mem κ).resolve_left hκV
  obtain ⟨c, hc⟩ := hφ 1 ⟨_, hi⟩ (by
    rw [← hθ, ← hθ]
    simp only [OneMemClass.coe_one, map_one, norm_one, map_inv₀, norm_inv]
    exact (one_le_inv₀ (norm_pos_iff.2 ((map_ne_zero θ).2 h0))).2 h₃)
  have : κ⁻¹ * c = 1 := (congrArg Subtype.val hc).symm
  exact hκV ((inv_mul_eq_one₀ h0).1 this ▸ c.2)

private theorem UpperTheory.exists_left_inverse_residue_injective {R : Type} [CommRing R] [IsLocalRing R] {n m : ℕ} (A : Matrix (Fin n) (Fin m) R)
    (h : Function.Injective (A.map (residue R)).mulVec) : ∃ B : Matrix (Fin m) (Fin n) R, B * A = 1 := by
  obtain ⟨B₀, hB₀⟩ := Guard.exists_left_inv _ h
  choose B₁ hB₁ using fun i j => residue_surjective (B₀ i j)
  let B : Matrix (Fin m) (Fin n) R := Matrix.of B₁
  have e : B.map (residue R) = B₀ := by ext i j; exact hB₁ i j
  have hd : IsUnit (B * A).det := by
    rw [← isUnit_map_iff (residue R), RingHom.map_det, RingHom.mapMatrix_apply, Matrix.map_mul, e, hB₀, Matrix.det_one]
    exact isUnit_one
  exact ⟨(B * A)⁻¹ * B, by rw [Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hd]⟩

private theorem UpperTheory.proper_extend_valuationSubring {K O : Type} [Field K] [CommRing O] {X : Scheme.{0}} (s : X ⟶ Sp O) [IsProper s]
    {A R : ValuationSubring K} (h : A ≤ R) (a : Sp R ⟶ X) (σ : O →+* A)
    (ha : a ≫ s = spMap ((A.inclusion R h).comp σ)) : ∃ a' : Sp A ⟶ X, spMap (A.inclusion R h) ≫ a' = a := by
  have hv : ValuativeCriterion.Existence s := by
    have h := (UniversallyClosed.eq_valuativeCriterion ▸ (inferInstance : UniversallyClosed s) :
      (ValuativeCriterion.Existence ⊓ @QuasiCompact : MorphismProperty Scheme) s)
    exact h.1
  let S : ValuativeCommSq s :=
    { R := A, K := K, i₁ := spMap R.subtype ≫ a, i₂ := spMap σ
      commSq := ⟨by
        rw [Category.assoc, ha, UpperTheory.spMap_comp_spMap_divisor_frames]
        exact (UpperTheory.spMap_comp_spMap_divisor_frames σ A.subtype).symm⟩ }
  obtain ⟨⟨a', h1, h2⟩⟩ := (hv S).exists_lift
  refine ⟨a', ?_⟩
  have : IsDominant (spMap R.subtype) := ⟨(PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical _).2
    (((RingHom.injective_iff_ker_eq_bot _).1 R.subtype_injective).le.trans bot_le)⟩
  refine ext_of_isDominant_of_isSeparated s ?_ (spMap R.subtype) ?_
  · rw [Category.assoc, ha, h2]
    exact UpperTheory.spMap_comp_spMap_divisor_frames _ _
  · rw [← Category.assoc, UpperTheory.spMap_comp_spMap_divisor_frames]
    exact h1

private theorem UpperTheory.preimage_open_local_top {R : Type} [CommRing R] [IsLocalRing R] {X : Scheme.{0}} (a : Sp R ⟶ X) {U : X.Opens}
    (h : a (closedPoint R) ∈ U) : ⊤ ≤ a ⁻¹ᵁ U := fun q _ =>
  ((IsLocalRing.specializes_closedPoint q).map a.continuous).mem_open U.isOpen h

private theorem UpperTheory.valuation_unit_section_one {K : Type} [Field K] (R : ValuationSubring K) {X : Scheme.{0}} (a : Sp R ⟶ X)
    {U : X.Opens} (h : a (closedPoint R) ∈ U) (g : Γ(X, U)ˣ) :
    R.valuation (valF (spMap R.subtype ≫ a) U g.val) = 1 := by
  obtain ⟨V, hV, hz, hle⟩ := exists_isAffineOpen_mem_and_subset (X := X) h
  obtain ⟨χ, rfl⟩ := exists_fromSpec hV a (UpperTheory.preimage_open_local_top a hz)
  rw [← Category.assoc, UpperTheory.spMap_comp_spMap_divisor_frames, ← valF_restrict hle (le_of_fromSpec hV rfl), valF_fromSpec]
  exact R.valuation_unit ((g.isUnit.map _).map χ).unit

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {X : Scheme.{0}}
  {t : SAB H X}

private theorem UpperTheory.lattice_graded_left_inverse {C : Type} [NontriviallyNormedField C] [IsUltrametricDist C] {x : Sp C ⟶ X}
    {Λ : Set (Sp (DualNumber C) ⟶ t.G.left)} {m n : ℕ} {u : Fin m → (Sp (DualNumber C) ⟶ t.G.left)}
    {v : Fin n → (Sp (DualNumber C) ⟶ t.G.left)} (hv : ∀ k, IsTanAtG t x (v k))
    (hL : ∀ cf w, IsCombAtG t x v cf w → (w ∈ Λ ↔ ∀ j, ‖cf j‖ ≤ 1))
    (A : Matrix (Fin n) (Fin m) C) (B : Matrix (Fin m) (Fin n) C) (hB : B * A = 1)
    (ha : ∀ i, IsCombAtG t x v (fun j => A j i) (u i)) {c : C} (hc : c ≠ 0) (h1 : ∀ j i, ‖c * A j i‖ ≤ 1)
    (h2 : ∀ i j, ‖c * B i j‖ ≤ 1) (i : Fin m) : ‖c‖ ≤ grNorm t x Λ u i ∧ grNorm t x Λ u i ≤ ‖c‖⁻¹ := by
  have hu := fun i => Guard.comb_tan hv (ha i)
  have hmem : ‖c‖⁻¹ ∈ Guard.grSet t x Λ u i := by
    obtain ⟨w, -, hw⟩ := Guard.exists_comb hu (Pi.single i c)
    refine ⟨Pi.single i c, by simpa using hc, fun k hk => Pi.single_eq_of_ne hk.ne' _,
      ⟨w, (hL _ w (tanLinG v hv u A _ w ha hw)).2 fun j => ?_, hw⟩, by simp⟩
    have h6 : A.mulVec (Pi.single i c) j = A j i * c := by
      rw [Matrix.mulVec_single]
      rfl
    rw [h6, mul_comm]
    exact h1 j i
  have hK : ∀ r ∈ Guard.grSet t x Λ u i, ‖c‖ ≤ r := by
    rintro _ ⟨cf, h0, -, ⟨w, hw, hc'⟩, rfl⟩
    have h7 := (hL _ w (tanLinG v hv u A cf w ha hc')).1 hw
    have h8 : cf i = ∑ j, B i j * A.mulVec cf j := by
      have := congrFun (Matrix.mulVec_mulVec cf B A) i
      rw [hB, Matrix.one_mulVec] at this
      exact this.symm
    have h9 : ‖c * cf i‖ ≤ 1 := by
      rw [h8, Finset.mul_sum]
      refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one fun j _ => ?_
      rw [← mul_assoc, norm_mul]
      exact mul_le_one₀ (h2 i j) (norm_nonneg _) (h7 j)
    rw [norm_mul] at h9
    rw [← one_div, le_div_iff₀ (norm_pos_iff.2 h0)]
    exact h9
  exact ⟨le_csInf ⟨_, hmem⟩ hK, csInf_le ⟨_, hK⟩ hmem⟩

private theorem UpperTheory.integral_tangent_lattice {C : Type} [NontriviallyNormedField C] [IsUltrametricDist C] {xO : Sp ↥(intO C) ⟶ X}
    (huniq : ∀ xO' : Sp ↥(intO C) ⟶ X, spMap (intO C).subtype ≫ xO' = spMap (intO C).subtype ≫ xO → xO' = xO)
    {n : ℕ} {D : Fin n → (Sp (DualNumber ↥(intO C)) ⟶ t.G.left)} (hD : ∀ e, IsTanAtG t xO (D e))
    (hD0 : ∀ w, IsTanAtG t xO w → ∃! a : Fin n → ↥(intO C), IsCombAtG t xO D a w)
    (hD1 : ∀ w, IsTanAtG t (spMap (intO C).subtype ≫ xO) w → ∃! a : Fin n → C,
      IsCombAtG t (spMap (intO C).subtype ≫ xO) (fun e => spMap (dualMap (intO C).subtype) ≫ D e) a w)
    (cf : Fin n → C) (w : Sp (DualNumber C) ⟶ t.G.left)
    (hw : IsCombAtG t (spMap (intO C).subtype ≫ xO) (fun e => spMap (dualMap (intO C).subtype) ≫ D e) cf w) :
    w ∈ latDR t (spMap (intO C).subtype ≫ xO) ↔ ∀ i, ‖cf i‖ ≤ 1 := by
  have hDk := fun j => GlobalTheory.FactorDepth.isTanAtG_map t (intO C).subtype (hD j)
  refine ⟨?_, fun hc => ?_⟩
  · rintro ⟨xO', hx, vO, hv, rfl⟩
    obtain rfl := huniq xO' hx
    obtain ⟨a, ha, -⟩ := hD0 vO hv
    have e := (hD1 _ (GlobalTheory.FactorDepth.isTanAtG_map t (intO C).subtype hv)).unique hw
      (GlobalTheory.LatDRFree.comb_map t (intO C).subtype ha)
    intro i
    rw [e]
    exact (a i).2
  · let a : Fin n → ↥(intO C) := fun i => ⟨cf i, hc i⟩
    obtain ⟨w', h1, ha⟩ := Guard.exists_comb hD a
    exact ⟨xO, rfl, w', h1, Guard.comb_unique hDk (GlobalTheory.LatDRFree.comb_map t (intO C).subtype ha) hw⟩

private theorem UpperTheory.tangent_finite_coordinates {Dw : Datum H} {l : Level H} {c : Coeff l} {S R : Type} [CommRing S] [IsLocalRing S]
    [CommRing R] [IsLocalRing R] (x : Sp S ⟶ X) (β : S →+* R) {φ : c.F →+* R} {f : Vecs Dw t R}
    (hf : LocM.IsFrame t φ (spMap β ≫ x) f) (τ : E →+* ℂ) (i : Fin (Dw.mult τ)) :
    ∃ s : Set R, s.Finite ∧ ∀ (C : Type) [NontriviallyNormedField C] [IsUltrametricDist C] (ψ : S →+* ↥(intO C))
      (θ : R →+* C), θ.comp β = (intO C).subtype.comp ψ →
      (∀ xO' : Sp ↥(intO C) ⟶ X, spMap (intO C).subtype ≫ xO' = spMap (intO C).subtype ≫ spMap ψ ≫ x →
        xO' = spMap ψ ≫ x) → ∀ d : C, d ≠ 0 → (∀ r ∈ s, ‖d * θ r‖ ≤ 1) →
      ‖d‖ ≤ grNorm t (spMap θ ≫ spMap β ≫ x) (latDR t (spMap θ ≫ spMap β ≫ x)) (f.bc θ τ) i ∧
        grNorm t (spMap θ ≫ spMap β ≫ x) (latDR t (spMap θ ≫ spMap β ≫ x)) (f.bc θ τ) i ≤ ‖d‖⁻¹ := by
  obtain ⟨n, D, hD, hDb⟩ := GlobalTheory.LieLocBasis.exists_lie_basis_stable E H X t S x
  choose a ha using fun k => (hDb R β _ (hf.1 τ k).1).exists
  let A : Matrix (Fin n) (Fin (Dw.mult τ)) R := fun j k => a k j
  have hA (T : Type) [CommRing T] (θ : R →+* T) (k) : IsCombAtG t (spMap (θ.comp β) ≫ x)
      (fun e => spMap (dualMap (θ.comp β)) ≫ D e) (fun j => A.map θ j k) (f.bc θ τ k) := by
    have := GlobalTheory.LatDRFree.comb_map t θ (ha k)
    simp only [← Category.assoc, UpperTheory.spMap_comp_spMap_divisor_frames β θ, UpperTheory.spMap_dualMap_comp_eq_spMap_dualMap_ringHom_comp β θ] at this
    exact this
  have hT (T : Type) [CommRing T] (χ : S →+* T) (e) := GlobalTheory.FactorDepth.isTanAtG_map t χ (hD e)
  obtain ⟨B, hB⟩ := UpperTheory.exists_left_inverse_residue_injective A (by
    refine (Guard.indep_iff (hT _ _) (Guard.indep_of_basis (hT _ _) (hDb _ _)) _ (hA _ (residue R))).1 ?_
    have := (frame_ind (GlobalTheory.T.isFrame_compose_ringHom_baseChange E H Dw _ _ _ _ _ _ _ (residue R) _ _ hf) τ).2
    rwa [← Category.assoc, UpperTheory.spMap_comp_spMap_divisor_frames] at this)
  refine ⟨Set.range (fun q : _ × _ => A q.1 q.2) ∪ Set.range (fun q : _ × _ => B q.1 q.2),
    (Set.finite_range _).union (Set.finite_range _), fun C _ _ ψ θ e hu d hd hs => ?_⟩
  have hL := UpperTheory.integral_tangent_lattice hu (hT _ ψ) (hDb _ ψ) (by
    simp only [← Category.assoc, UpperTheory.spMap_comp_spMap_divisor_frames ψ, UpperTheory.spMap_dualMap_comp_eq_spMap_dualMap_ringHom_comp ψ]
    exact hDb _ _)
  simp only [← Category.assoc, UpperTheory.spMap_comp_spMap_divisor_frames ψ, UpperTheory.spMap_dualMap_comp_eq_spMap_dualMap_ringHom_comp ψ, ← e] at hL
  rw [← Category.assoc, UpperTheory.spMap_comp_spMap_divisor_frames]
  exact UpperTheory.lattice_graded_left_inverse (hT _ _) hL (A.map θ) (B.map θ)
    (by rw [← Matrix.map_mul, hB, Matrix.map_one _ (map_zero θ) (map_one θ)]) (hA C θ) hd
    (fun j k => hs _ (Or.inl ⟨(j, k), rfl⟩)) (fun j k => hs _ (Or.inr ⟨(j, k), rfl⟩)) i

private theorem UpperTheory.countable_essFiniteType (K : Type) [Field K] [Algebra.EssFiniteType ℤ K] : Countable K := by
  let S := Algebra.EssFiniteType.subalgebra ℤ K
  obtain ⟨n, g, hg⟩ := Algebra.FiniteType.iff_quotient_mvPolynomial''.1 (inferInstance : Algebra.FiniteType ℤ S)
  have : Countable (MvPolynomial (Fin n) ℤ) := by
    rw [← Cardinal.mk_le_aleph0_iff]
    exact MvPolynomial.cardinalMk_le_max.trans (max_le (max_le Cardinal.mk_le_aleph0 Cardinal.mk_le_aleph0) le_rfl)
  have : Countable S := hg.countable
  rw [← Cardinal.mk_le_aleph0_iff]
  exact (IsLocalization.cardinalMk_le (Algebra.EssFiniteType.submonoid ℤ K)).trans Cardinal.mk_le_aleph0

private theorem UpperTheory.exists_uniform_prime_power {K : Type} [Field K] {A R : ValuationSubring K} {p : ℕ}
    (h : ∀ x ∈ R, ∃ m : ℕ, (p : K) ^ m * x ∈ A) {s : Set R} (hs : s.Finite) :
    ∃ m : ℕ, ∀ x ∈ s, (p : K) ^ m * x ∈ A := by
  choose g hg using fun x : R => h x x.2
  obtain ⟨m, hm⟩ := (hs.image g).bddAbove
  refine ⟨m, fun x hx => ?_⟩
  obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le' (hm ⟨x, hx, rfl⟩)
  rw [hk, pow_add, mul_assoc]
  exact mul_mem (pow_mem (natCast_mem A p) k) (hg x)

end SlopeTestRemainingChoices

open Formalism.MainNotions.DIV.Cons GlobalTheory.FieldPtGlue GlobalTheory.ShFam.Pad.Pull in
theorem UpperTheory.line_model_integral_lattice :
    ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H} {Xo : ∀ l : Level H, Moduli Dw l} {p : ℕ} {W : ValuationSubring ℂ} {Y : LocalSystem Xo p W} {i₀ : Idx H p}, p.Prime → (p : ℂ) ∈ W.nonunits → ∀ (Z : LocM.Mdl Y i₀) (x : Letter Dw) (M : LineModel Z false (.inl (x.1, (x.2 : ℕ))) x) (K : Type) [Field K] (R : ValuationSubring K), Algebra.EssFiniteType ℤ K → ∀ (a : Sp R ⟶ Z.X) (φR : Z.i.c.F →+* R), a ≫ Z.s = spMap φR ≫ spMap (Z.i.c.V W).subtype → ∀ f : Vecs Dw (Y Z.i).t R, LocM.IsFrame (Y Z.i).t φR (a ≫ Z.π) f → ∀ (a₀ : Fin Z.m) (φ : Γ(Z.X, (Z.U a₀).1) →+* K), spMap φ ≫ Z.chart a₀ = spMap R.subtype ≫ a → ∀ t : Fin (Dw.mult x.1) → K, (∀ i, ∃ cf : Fin (Dw.mult x.1) → K, cf i = t i ∧ (∀ m, i < m → cf m = 0) ∧ IsCombAtG (Y Z.i).t (spMap R.subtype ≫ a ≫ Z.π) (f.bc R.subtype x.1) cf ((Z.fr a₀).bc φ x.1 i)) → ∀ i : Fin M.L.n, a (closedPoint R) ∈ M.L.U i → R.valuation (valF (spMap R.subtype ≫ a) _ (M.r a₀ i).val * t x.2) = 1 := by
  intro E _ _ _ H Dw Xo p W Y i₀ hp hW Z x M K _ R hK a φR ha f hf a₀ φ hφ t ht i hi
  have := Z.i.c.fin
  have : NumberField Z.i.c.F := {}
  have := UpperTheory.countable_essFiniteType K
  have : CharZero K := (R.subtype.comp φR).charZero_iff (RingHom.injective _) |>.1 inferInstance
  have hp0 : (p : K) ≠ 0 := Nat.cast_ne_zero.2 hp.ne_zero
  obtain ⟨A, hAR, hVA, hpA, hA⟩ := UpperTheory.exists_valuationSubring_below p Z.i.c.F K R φR (Z.i.c.V W) hp (natCast_mem_nonunits_V _ hp hW)
  have := isProper_str (Z.i.c.V W) Z.n
  have : IsProper Z.s := inferInstanceAs (IsProper (_ ≫ _))
  have := isDiscreteValuationRing_V Z.i.c hp hW
  have : IsLocallyNoetherian Z.X := LocallyOfFiniteType.isLocallyNoetherian Z.s
  obtain ⟨a', ha'⟩ := UpperTheory.proper_extend_valuationSubring Z.s hAR a
    (((R.subtype.comp φR).comp (Z.i.c.V W).subtype).codRestrict A fun v => hVA v v.2)
    (ha.trans (UpperTheory.spMap_comp_spMap_divisor_frames _ _))
  obtain ⟨j, hj⟩ := LB.mem_of_cover M.L.isLB (a' (closedPoint A))
  let B : Type := Z.X.presheaf.stalk (a' (closedPoint A))
  let ι : Sp B ⟶ Z.X := Z.X.fromSpecStalk _
  have hι (q : Sp B) : ι q ∈ M.L.U j :=
    ((Z.X.range_fromSpecStalk (x := a' (closedPoint A))).le ⟨q, rfl⟩).mem_open (M.L.U j).isOpen hj
  let β₀ : B →+* A := (Scheme.stalkClosedPointTo a').hom
  let β : B →+* R := (A.inclusion R hAR).comp β₀
  have hβ : spMap β ≫ ι = a := by
    rw [← ha', ← UpperTheory.spMap_comp_spMap_divisor_frames, Category.assoc]
    exact congrArg _ (Scheme.Spec_stalkClosedPointTo_fromSpecStalk a')
  have hj' : a (closedPoint R) ∈ M.L.U j := by
    rw [← hβ]
    exact hι (spMap β (closedPoint R))
  have w₀ : ⊤ ≤ (spMap R.subtype ≫ a) ⁻¹ᵁ (Z.U a₀).1 := le_of_fromSpec (Z.U a₀).2 hφ
  have wi : ⊤ ≤ (spMap R.subtype ≫ a) ⁻¹ᵁ M.L.U i := fun q _ =>
    UpperTheory.preimage_open_local_top a hi (Set.mem_univ (spMap R.subtype q))
  have wj : ⊤ ≤ (spMap R.subtype ≫ a) ⁻¹ᵁ M.L.U j := fun q _ =>
    UpperTheory.preimage_open_local_top a hj' (Set.mem_univ (spMap R.subtype q))
  rw [M.trans K _ a₀ j i fun q hq => ⟨w₀ hq, wj hq, wi hq⟩, mul_assoc, map_mul,
    UpperTheory.valuation_unit_section_one R a (U := M.L.U j ⊓ M.L.U i) ⟨hj', hi⟩, one_mul]
  have hr := GenId.val_ne_zero M w₀ wj
  have I₁ := frame_ind (GlobalTheory.T.isFrame_compose_ringHom_baseChange E H Dw _ _ _ _ _ _ _ R.subtype _ _ hf) x.1
  have I₂ := frame_ind (chart_frame Z hφ) x.1
  rw [Category.assoc] at I₂
  have ht0 (k) : t k ≠ 0 := by
    obtain ⟨cf, c1, -, c2⟩ := ht k
    exact c1 ▸ (Pull.Tri.diag I₁ I₂ (fun k => (ht k).imp fun _ h => h.2) c2).1
  set u : K := valF (spMap R.subtype ≫ a) _ (M.r a₀ j).val * t x.2 with hu
  have hu0 : u ≠ 0 := mul_ne_zero hr (ht0 _)
  obtain ⟨s, hs, hS⟩ := UpperTheory.tangent_finite_coordinates (ι ≫ Z.π) β (f := f) (φ := φR) (by rwa [← Category.assoc, hβ]) x.1 x.2
  obtain ⟨m, hm⟩ := UpperTheory.exists_uniform_prime_power hA hs
  letI : Algebra B K := (R.subtype.comp β).toAlgebra
  have : Algebra.EssFiniteType B K := Algebra.EssFiniteType.of_comp ℤ B K
  have key (C : SCF p) (ψ : B →+* ↥(intO ↥C.S)) (θ : K →+* ↥C.S)
      (e : θ.comp (algebraMap B K) = (intO ↥C.S).subtype.comp ψ)
      (h : ∀ y ∈ (fun r : R => (p : K) ^ m * r) '' s, ‖θ y‖ ≤ 1) :
      ‖θ ((p : K) ^ m * u)‖ ≤ 1 ∧ ‖θ ((p : K) ^ m * u⁻¹)‖ ≤ 1 := by
    have hd : θ ((p : K) ^ m) ≠ 0 := (map_ne_zero θ).2 (pow_ne_zero _ hp0)
    obtain ⟨b1, b2⟩ := hS _ ψ (θ.comp R.subtype) e (fun xO' h => ext_unique _ _ _ h) _ hd fun r hr => by
      have := h _ ⟨r, hr, rfl⟩
      rwa [map_mul] at this
    have g : spMap (intO ↥C.S).subtype ≫ spMap ψ ≫ ι = spMap θ ≫ spMap R.subtype ≫ a := by
      rw [← hβ, ← Category.assoc, UpperTheory.spMap_comp_spMap_divisor_frames, ← e, ← Category.assoc, ← Category.assoc, UpperTheory.spMap_comp_spMap_divisor_frames,
        UpperTheory.spMap_comp_spMap_divisor_frames]
    obtain ⟨Q, hQ⟩ := ModelPt.exists_ptC E H Dw Xo p W Y i₀ hp hW Z C (spMap ψ ≫ ι) (by
      rintro _ ⟨q, rfl⟩
      rw [g, ← Z.cover]
      exact Set.mem_iUnion.2 ⟨a₀, w₀ (Set.mem_univ (spMap θ q))⟩)
    let y : Z.Pt := ⟨C, Q, spMap ψ ≫ ι, hQ⟩
    have hy : y.gen = spMap θ ≫ spMap R.subtype ≫ a := g
    have hn := M.norm y a₀ j (θ.comp φ) (by rw [hy, ← hφ, ← Category.assoc, UpperTheory.spMap_comp_spMap_divisor_frames])
      fun q _ => hι (spMap ψ q)
    have e1 : spMap (θ.comp R.subtype) ≫ spMap β ≫ ι ≫ Z.π = spMap θ ≫ spMap R.subtype ≫ a ≫ Z.π := by
      rw [← UpperTheory.spMap_comp_spMap_divisor_frames, Category.assoc, reassoc_of% hβ]
    rw [e1] at b1 b2
    have e2 : f.bc (θ.comp R.subtype) x.1 = fun k => spMap (dualMap θ) ≫ f.bc R.subtype x.1 k := by
      funext k
      simp only [Vecs.bc, ← Category.assoc, UpperTheory.spMap_dualMap_comp_eq_spMap_dualMap_ringHom_comp]
    have e3 : (Z.fr a₀).bc (θ.comp φ) x.1 = fun k => spMap (dualMap θ) ≫ (Z.fr a₀).bc φ x.1 k := by
      funext k
      simp only [Vecs.bc, ← Category.assoc, UpperTheory.spMap_dualMap_comp_eq_spMap_dualMap_ringHom_comp]
    rw [e2] at b1 b2
    rw [hy, GenId.valF_map θ (U := (Z.U a₀).1 ⊓ M.L.U j) fun q hq => ⟨w₀ hq, wj hq⟩] at hn
    simp only [lnStep, lat, dif_pos x.2.2, Bool.false_eq_true, false_and, if_false, sub_zero, Category.assoc,
      Fin.eta] at hn
    rw [e3, Guard.grNorm_tri (d := fun k => θ (t k)) (fun k => GlobalTheory.FactorDepth.isTanAtG_map _ θ (I₁.1 k))
      (fun k => (map_ne_zero θ).2 (ht0 k)) (fun k => by
        obtain ⟨cf, c1, c2, c3⟩ := ht k
        exact ⟨fun a => θ (cf a), congrArg θ c1, fun a ha => (congrArg θ (c2 a ha)).trans (map_zero θ),
          GlobalTheory.LatDRFree.comb_map _ θ c3⟩)] at hn
    have d0 := norm_pos_iff.2 hd
    have g0 := d0.trans_le b1
    have r0 := norm_pos_iff.2 ((map_ne_zero θ).2 hr)
    have t0 := norm_pos_iff.2 ((map_ne_zero θ).2 (ht0 x.2))
    rw [← Real.log_mul r0.ne' (mul_pos t0 g0).ne', ← mul_assoc, ← norm_mul, ← map_mul, ← hu] at hn
    have u0 := norm_pos_iff.2 ((map_ne_zero θ).2 hu0)
    have e4 := Real.eq_one_of_pos_of_log_eq_zero (mul_pos u0 g0) hn
    rw [map_mul θ _ u, map_mul θ _ u⁻¹, norm_mul, norm_mul, map_inv₀, norm_inv, ← eq_inv_of_mul_eq_one_right e4]
    constructor
    · rw [← e4, mul_comm]
      exact mul_le_mul_of_nonneg_left b1 u0.le
    · rw [← mul_inv_cancel₀ d0.ne']
      exact mul_le_mul_of_nonneg_left b2 d0.le
  have hB : ∀ r, algebraMap B K r ∈ A := fun r => (β₀ r).2
  have hsA : ∀ y ∈ (fun r : R => (p : K) ^ m * r) '' s, y ∈ A := by
    rintro _ ⟨r, hr, rfl⟩
    exact hm r hr
  have k1 := hAR (UpperTheory.spherical_completion_integral hp A hB hpA (hs.image _) hsA fun C ψ θ e h => (key C ψ θ e h).1)
  have k2 := hAR (UpperTheory.spherical_completion_integral hp A hB hpA (hs.image _) hsA fun C ψ θ e h => (key C ψ θ e h).2)
  have hv : R.valuation ((p : K) ^ m) = 1 := by
    have := R.valuation_unit ((((Nat.cast_ne_zero.2 hp.ne_zero : (p : Z.i.c.F) ≠ 0).isUnit).map φR).unit)
    rw [map_pow, show R.valuation (p : K) = 1 by simpa using this, one_pow]
  replace k1 := (R.valuation_le_one_iff _).2 k1
  replace k2 := (R.valuation_le_one_iff _).2 k2
  rw [map_mul, hv, one_mul] at k1 k2
  rw [map_inv₀] at k2
  exact le_antisymm k1 ((inv_le_one₀ (zero_lt_iff.2 ((map_ne_zero _).2 hu0))).1 k2)
