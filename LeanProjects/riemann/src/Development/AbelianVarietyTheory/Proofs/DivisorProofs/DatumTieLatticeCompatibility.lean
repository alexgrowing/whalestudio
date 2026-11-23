import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.LieInj
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ScholzeWeinsteinB
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.EpsilonPairingZeta
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.HodgeTateKernel
import Development.AbelianVarietyTheory.Definitions.Divisors.TorsionTowersOfDivisibleGroup
import Development.AbelianVarietyTheory.Definitions.Divisors.IsLatBasisHtLatIffSpanEq
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SandwichKernelRangeExactStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralFunctionalExtensionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DatumTieNumberFieldPointStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EigenspacesOfRingHomsIndependent
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntertwinerMapsEigenspaces
open GlobalTheory GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps GlobalTheory.DetInv GlobalTheory.HTLat GlobalTheory.CompHt GlobalTheory.PDivGroup Matrix TensorProduct NumberField CategoryTheory

namespace GlobalTheory.DetInv.Duality

section Abstract

variable {C : Type} [Field C] {v : Valuation C NNReal} {O : Type} [CommRing O] [Algebra O C]
  {V : Type} [AddCommGroup V] [Module C V] [Module O V] [IsScalarTower O C V] {h q : ℕ}

theorem isBasisOf_dual (hv : v.Integers O) (B : V →ₗ[C] V →ₗ[C] C)
    (rep : ∀ F : V →ₗ[C] C, ∃ x, ∀ w, B w x = F w) (e : V →ₗ[C] V) (A : V →ₗ[C] (Fin h → C))
    (S U : Submodule C V) (heU : ∀ x, e x ∈ U) (heS : ∀ w ∈ S, ∀ x, B w (e x) = B w x)
    (k1 : ∀ w ∈ S, ∀ x, A x = 0 → B w x = 0)
    (k2 : ∀ x ∈ U, (∀ w ∈ S, B w x = 0) → A x = 0)
    (L : Submodule O V) (hL : L.FG) (hLS : ∀ w ∈ S, ∃ a : O, a ≠ 0 ∧ a • w ∈ L)
    (z : Fin q → V) (hz : Submodule.span O (Set.range z) = L ⊓ S.restrictScalars O)
    (x : Fin q → V) (hxU : ∀ j, x j ∈ U) (hx : ∀ i j, B (z i) (x j) = if i = j then 1 else 0)
    (M : Submodule O (Fin h → C))
    (hM : ∀ m, m ∈ M ↔ ∃ t, (∀ w ∈ L, B w t ∈ (algebraMap O C).range) ∧ A (e t) = m) :
    IsBasisOf C M (fun j => A (x j)) := by
  have hzm : ∀ i, z i ∈ L ⊓ S.restrictScalars O := fun i => hz.le (Submodule.subset_span ⟨i, rfl⟩)
  have k3 : ∀ t ∈ U, (∀ w ∈ L, w ∈ S → B w t = 0) → A t = 0 := by
    intro t ht H
    refine k2 t ht fun w hw => ?_
    obtain ⟨a, ha, haw⟩ := hLS w hw
    have h1 := H _ haw (by rw [← algebraMap_smul C a]; exact S.smul_mem _ hw)
    rw [← algebraMap_smul C a, map_smul, LinearMap.smul_apply, smul_eq_mul] at h1
    exact (mul_eq_zero.1 h1).resolve_left fun h0 => ha (hv.hom_inj (by rw [h0, map_zero]))
  have hsum : ∀ (c : Fin q → C) (i : Fin q), B (z i) (∑ j, c j • x j) = c i := by
    intro c i
    simp [map_sum, hx]
  refine ⟨Fintype.linearIndependent_iff.2 fun c hc i => ?_, le_antisymm ?_ fun m hm => ?_⟩
  · rw [← hsum c i]
    exact k1 _ (hzm i).2 _ (by simpa [map_sum] using hc)
  · rw [Submodule.span_le]
    rintro _ ⟨j, rfl⟩
    obtain ⟨F, hF, hF'⟩ := GlobalTheory.T.integral_functional_extension C v O V L S (B.flip (x j)) hv hL (by
      intro w hw hw'
      obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun O).1 (hz.ge ⟨hw, hw'⟩)
      refine ⟨c j, ?_⟩
      have e1 : ∀ i, B (c i • z i) (x j) = if i = j then algebraMap O C (c i) else 0 := fun i => by
        rw [← algebraMap_smul C (c i), map_smul, LinearMap.smul_apply, hx, smul_eq_mul, mul_ite,
          _root_.mul_one, mul_zero]
      rw [LinearMap.flip_apply, map_sum, LinearMap.sum_apply]
      simp only [e1, Finset.sum_ite_eq', Finset.mem_univ, if_true])
    obtain ⟨t, ht⟩ := rep F
    refine (hM _).2 ⟨t, fun w hw => ht w ▸ hF w hw, ?_⟩
    rw [← sub_eq_zero, ← map_sub]
    refine k3 _ (U.sub_mem (heU t) (hxU j)) fun w hw hw' => ?_
    rw [map_sub, heS w hw', ht, hF' w hw hw', LinearMap.flip_apply, sub_self]
  · obtain ⟨t, ht, rfl⟩ := (hM m).1 hm
    choose c hc using fun i => ht (z i) (hzm i).1
    have h0 : A (e t - ∑ j, algebraMap O C (c j) • x j) = 0 := by
      refine k3 _ (U.sub_mem (heU t) (U.sum_mem fun j _ => U.smul_mem _ (hxU j))) fun w hw hw' => ?_
      obtain ⟨d, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun O).1 (hz.ge ⟨hw, hw'⟩)
      rw [map_sum, LinearMap.sum_apply]
      refine Finset.sum_eq_zero fun i _ => ?_
      rw [← algebraMap_smul C (d i), map_smul, LinearMap.smul_apply, map_sub, hsum,
        heS _ (hzm i).2, hc, sub_self, smul_zero]
    rw [map_sub, sub_eq_zero] at h0
    rw [h0, map_sum]
    refine Submodule.sum_mem _ fun j _ => ?_
    rw [map_smul, algebraMap_smul]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)

omit [Module O V] [IsScalarTower O C V] in

theorem exists_dual_family (B : V →ₗ[C] V →ₗ[C] C)
    (rep : ∀ F : V →ₗ[C] C, ∃ x, ∀ w, B w x = F w) (z : Fin q → V) (hz : LinearIndependent C z) :
    ∃ x : Fin q → V, ∀ i j, B (z i) (x j) = if i = j then 1 else 0 := by
  have : ∀ j, ∃ x, ∀ i, B (z i) x = if i = j then 1 else 0 := by
    intro j
    obtain ⟨F, hF⟩ := LinearMap.exists_extend ((Module.Basis.span hz).coord j)
    obtain ⟨x, hx⟩ := rep F
    refine ⟨x, fun i => ?_⟩
    have := LinearMap.congr_fun hF (Module.Basis.span hz i)
    rw [Module.Basis.coord_apply, Module.Basis.repr_self, Finsupp.single_apply,
      LinearMap.comp_apply, Submodule.subtype_apply, Module.Basis.span_apply] at this
    rw [hx, this]
  choose x hx using this
  exact ⟨x, fun i j => hx j i⟩

theorem eq_zero_of_forall_mul_mem (hv : v.Integers O) {a : O} (ha : ¬IsUnit a)
    (ha0 : algebraMap O C a ≠ 0) {s : C} (hs : ∀ c : C, c * s ∈ (algebraMap O C).range) : s = 0 := by
  by_contra h0
  obtain ⟨b, hb⟩ := hs ((algebraMap O C a)⁻¹ * s⁻¹)
  refine ha (IsUnit.of_mul_eq_one b (hv.hom_inj ?_))
  rw [map_mul, hb, map_one]
  field_simp

end Abstract

section Datum

variable {p : ℕ} [Fact p.Prime] {O : Type} [CommRing O] [Fact ¬IsUnit (p : O)]
  [IsAdicComplete (Ideal.span {(p : O)}) O] (C : Type) [Field C] [Algebra O C]
  {ε : PreTilt O p} {h : ℕ} {Γ : Type} [CommRing Γ] [Algebra ℤ_[p] Γ] (D : Datum ε h Γ)

theorem bC_incl (u : Fin h → O) : bC C D (incl C h u) = incl C h (D.bb u) := by
  funext i
  simp [bC, redC, incl, Datum.bb, Matrix.mulVec, dotProduct, map_sum]

theorem alC_mem_eig (σ : Γ →+* O) {u : Fin h → C} (hu : u ∈ eig C (actT D) σ) :
    alC C D u ∈ eig C (actH D) σ := by
  have hX : ∀ l, D.F.map (WittVector.fontaineTheta O p) * actT D l =
      actH D l * D.F.map (WittVector.fontaineTheta O p) := by
    intro l
    have := congrArg (fun X => X.map (WittVector.fontaineTheta O p)) (D.F_act l)
    simp only [Matrix.map_mul] at this
    exact this
  exact (eig_map_equivariant C O Γ h _ _ _ hX).1 σ (Submodule.mem_map_of_mem hu)

theorem disjoint_eigH (hi : Function.Injective (algebraMap O C)) (σ : Γ →+* O) :
    Disjoint (eig C (actH D) σ) (⨆ τ : {τ : Γ →+* O // τ ≠ σ}, eig C (actH D) τ.1) := by
  have := GlobalTheory.iSupIndep_eig C O Γ h
    ((RingHom.mapMatrix (WittVector.fontaineTheta O p)).comp D.ρM) hi σ
  rw [iSup_subtype'] at this
  exact this

end Datum

section Pt

variable {p : ℕ} [Fact p.Prime] {C : Type} [Field C] {v : Valuation C NNReal} {O : Type}
  [CommRing O] [Algebra O C] {Λ : Type} [CommRing Λ] [StarRing Λ] [Algebra ℤ_[p] C]
  [IsAlgClosed C] [CharZero C] (P : Point p v O Λ)

theorem exists_pairV_eq (F : P.V →ₗ[C] C) : ∃ x, ∀ w, P.pairV w x = F w := by
  obtain ⟨x, hx, -⟩ := P.existsUnique_pairV
    ((F.restrictScalars ℤ_[p]) ∘ₗ TensorProduct.mk ℤ_[p] C P.T 1)
  refine ⟨-x, fun w => ?_⟩
  induction w using TensorProduct.induction_on with
  | zero => simp
  | add a b ha hb => rw [map_add, LinearMap.add_apply, ha, hb, map_add]
  | tmul c t =>
    have e : (c ⊗ₜ t : P.V) = c • (1 ⊗ₜ t) := by
      rw [TensorProduct.smul_tmul', smul_eq_mul, _root_.mul_one]
    rw [e, map_smul, map_smul, LinearMap.smul_apply, map_neg, ← P.pairV_swap, hx]
    rfl

theorem pairV_eq_zero {χ χ' : Λ →+* C} {w x : P.V} (hw : w ∈ EigenSplit.eigenSub P.actV χ)
    (hx : x ∈ EigenSplit.eigenSub P.actV χ') {a : Λ} (ha : χ a ≠ χ' (star a)) :
    P.pairV w x = 0 := by
  have h1 := P.pairV_act a w x
  rw [EigenSplit.mem_eigenSub.1 hw, EigenSplit.mem_eigenSub.1 hx, map_smul, map_smul,
    LinearMap.smul_apply, smul_eq_mul, smul_eq_mul] at h1
  exact (mul_eq_mul_right_iff.1 h1).resolve_left ha

variable [Algebra ℤ_[p] O] [IsScalarTower ℤ_[p] O C]

theorem mem_latT_iff_pair (t : P.V) :
    t ∈ P.latT ↔ ∀ w ∈ P.latT, P.pairV w t ∈ (algebraMap O C).range := by
  constructor
  · rintro ht _ ⟨w, rfl⟩
    induction w using TensorProduct.induction_on with
    | zero => simp
    | add a b ha hb => rw [map_add, map_add, LinearMap.add_apply]; exact add_mem ha hb
    | tmul c s =>
      obtain ⟨d, hd⟩ := (P.mem_latT_iff t).1 ht s
      have e : (algebraMap O C c ⊗ₜ s : P.V) = algebraMap O C c • (1 ⊗ₜ s) := by
        rw [TensorProduct.smul_tmul', smul_eq_mul, _root_.mul_one]
      refine ⟨-(c * d), ?_⟩
      rw [P.inclT_tmul, e, map_smul, LinearMap.smul_apply, P.pairV_swap, ← hd]
      simp
  · intro H
    refine (P.mem_latT_iff t).2 fun s => ?_
    obtain ⟨d, hd⟩ := H _ (P.one_tmul_mem_latT s)
    exact ⟨-d, by rw [map_neg, hd, ← P.pairV_swap]⟩

variable [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O]
  {ε : PreTilt O p} {h : ℕ} {Γ : Type} [CommRing Γ] [Algebra ℤ_[p] Γ] {P} {D : Datum ε h Γ}
  {j : Λ →+* Γ} {φ : P.V ≃ₗ[C] (Fin h → C)}

theorem latLie_le_W (T : IsTie P D j φ) (hε : IsPrimitiveRoot (root ε).untilt p) {x : P.V}
    (hx : x ∈ P.latLie) : x ∈ P.W := by
  obtain ⟨_, ⟨u, rfl⟩, hu⟩ := (T.lie x).1 hx
  rw [T.ker, ← hu, ← bC_incl]
  exact (GlobalTheory.T.sandwich_kernel_range_exact p C v O P.integers ε hε Γ h D).2.ge ⟨_, rfl⟩

theorem exists_smul_mem_latLie (T : IsTie P D j φ) (hε : IsPrimitiveRoot (root ε).untilt p)
    {x : P.V} (hx : x ∈ P.W) : ∃ a : O, a ≠ 0 ∧ a • x ∈ P.latLie := by
  obtain ⟨u, hu⟩ := (GlobalTheory.T.sandwich_kernel_range_exact p C v O P.integers ε hε Γ h D).2.le ((T.ker x).1 hx)
  obtain ⟨a, ha, hau⟩ := P.exists_smul_mem_latT (φ.symm u)
  choose u₀ hu₀ using (T.lat _).1 hau
  refine ⟨a, ha, (T.lie _).2 ⟨D.bb u₀, ⟨u₀, rfl⟩, ?_⟩⟩
  have e : incl C h u₀ = algebraMap O C a • u := by
    funext i
    refine (hu₀ i).trans ?_
    rw [← algebraMap_smul C a, map_smul, φ.apply_symm_apply]
  rw [← bC_incl, e, map_smul, hu, ← algebraMap_smul C a x, map_smul]

theorem alC_eq_zero_iff (T : IsTie P D j φ) (x : P.V) :
    alC C D (φ x) = 0 ↔ ∀ w ∈ P.latLie, P.pairV w x = 0 := by
  have hp : ¬IsUnit (p : O) := Fact.out
  have hp0 : algebraMap O C p ≠ 0 := by
    rw [map_natCast]; exact Nat.cast_ne_zero.2 (Fact.out : p.Prime).ne_zero
  constructor
  · intro H w hw
    refine eq_zero_of_forall_mul_mem P.integers hp hp0 fun c => ?_
    have := (T.fil (c • x)).1 (fun i => by rw [map_smul, map_smul, H]; simp) w hw
    rwa [map_smul, smul_eq_mul] at this
  · intro H
    funext i
    refine eq_zero_of_forall_mul_mem P.integers hp hp0 fun c => ?_
    have := (T.fil (c • x)).2 (fun w hw => by rw [map_smul, H w hw]; simp) i
    rwa [map_smul, map_smul, Pi.smul_apply, smul_eq_mul] at this

theorem fg_latLie (T : IsTie P D j φ) : P.latLie.FG := by
  have e : P.latLie = (D.Lie.map (incl C h)).map
      ((φ.symm : (Fin h → C) →ₗ[C] P.V).restrictScalars O) := by
    ext x
    rw [T.lie]
    constructor
    · exact fun hx => ⟨_, hx, φ.symm_apply_apply x⟩
    · rintro ⟨u, hu, rfl⟩
      simpa using hu
  rw [e]
  exact ((Module.Finite.iff_fg.1 (Module.Finite.range D.bb)).map _).map _

theorem wRec_eq (T : IsTie P D j φ) (hε : IsPrimitiveRoot (root ε).untilt p) (τ : Λ →+* O) :
    P.wRec τ = P.latLie ⊓ (P.eigW τ).restrictScalars O := by
  refine le_antisymm (fun x hx => ?_) ?_
  · have := P.wRec_le τ hx
    exact ⟨this.1, latLie_le_W T hε this.1, this.2⟩
  · rintro _ ⟨⟨x, rfl⟩, -, hx⟩
    refine ⟨⟨x, fun a => T.lieInj ?_⟩, rfl⟩
    rw [P.bLie_act, P.bLie_scale, EigenSplit.mem_eigenSub.1 hx a, RingHom.comp_apply,
      algebraMap_smul]

end Pt

theorem fil_al_dual : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [Algebra ℤ_[p] O] [Algebra ℤ_[p] C] [IsScalarTower ℤ_[p] O C] (E : Type) [Field E] [NumberField E] [StarRing (𝓞 E)] (P : Point p v O (𝓞 E)) (ε : PreTilt O p) (h : ℕ) (D : Datum ε h (ℤ_[p] ⊗[ℤ] 𝓞 E)) (φ : P.V ≃ₗ[C] (Fin h → C)), IsPrimitiveRoot (root ε).untilt p → IsTie P D (Algebra.TensorProduct.includeRight : 𝓞 E →ₐ[ℤ] ℤ_[p] ⊗[ℤ] 𝓞 E).toRingHom φ → ∀ (σ : ℤ_[p] ⊗[ℤ] 𝓞 E →+* O) (ψ : E →+* C), σ.comp (Algebra.TensorProduct.includeRight : 𝓞 E →ₐ[ℤ] ℤ_[p] ⊗[ℤ] 𝓞 E).toRingHom = embO P.integers ψ → ∀ (q : ℕ) (y : Fin q → P.V) (g' : Matrix (Fin q) (Fin q) C), Module.finrank C (P.eigW ((embO P.integers ψ).comp (starRingEnd (𝓞 E)))) = q → Submodule.span O (Set.range y) = P.wRec ((embO P.integers ψ).comp (starRingEnd (𝓞 E))) → IsLatBasis C (P.latTSub ((embO P.integers ψ).comp (starRingEnd (𝓞 E)))) (fun i => ∑ j, g' i j • y j) → ∃ (m : Fin q → Fin h → C) (k : Matrix (Fin q) (Fin q) C), IsBasisOf C (filQuot C D σ) m ∧ IsBasisOf C (alQuot C D σ) (fun i => ∑ j, k i j • m j) ∧ k.det * g'.det = 1 := by
  intro p _ C _ _ _ v O _ _ _ _ _ _ _ E _ _ _ P ε h D φ hε T σ ψ hσ q y g' hq hy hg
  classical
  have hv := P.integers
  obtain ⟨-, -, -, hE⟩ := GlobalTheory.T.datum_tie_number_field_point p C v O E P ε h D φ hε T
  obtain ⟨hE1, -, hE3, -⟩ := hE σ ψ hσ
  let sp := isSplitting_embO (E := E) hv
  let e : (E →+* C) → P.V →ₗ[C] P.V := fun i => EigenSplit.proj sp P.actV i
  have hemem : ∀ i x, e i x ∈ P.eigV (embO hv i) := fun i x => EigenSplit.proj_mem sp P.actV i x
  have hesum : ∀ x, ∑ i, e i x = x := fun x => EigenSplit.sum_proj sp P.actV x
  have hsplit : ∀ x, x - e ψ x = ∑ i ∈ Finset.univ.erase ψ, e i x := fun x => by
    rw [sub_eq_iff_eq_add, Finset.sum_erase_add _ _ (Finset.mem_univ ψ), hesum]
  have hinj : ∀ i i' : E →+* C, (∀ a, embO hv i a = embO hv i' a) → i = i' := fun i i' H =>
    IsLocalization.ringHom_ext (nonZeroDivisors (𝓞 E)) (RingHom.ext fun a => by
      have := congrArg (algebraMap O C) (H a)
      rwa [algebraMap_embO, algebraMap_embO] at this)
  set τ : 𝓞 E →+* O := (embO P.integers ψ).comp (starRingEnd (𝓞 E)) with hτ
  let A : P.V →ₗ[C] (Fin h → C) := alC C D ∘ₗ (φ : P.V →ₗ[C] (Fin h → C))
  have heS : ∀ w ∈ P.eigW τ, ∀ x, P.pairV w (e ψ x) = P.pairV w x := by
    intro w hw x
    rw [eq_comm, ← sub_eq_zero, ← map_sub, hsplit, map_sum]
    refine Finset.sum_eq_zero fun i hi => ?_
    obtain ⟨a, ha⟩ := not_forall.1 fun H => Finset.ne_of_mem_erase hi (hinj i ψ H)
    refine pairV_eq_zero P hw.2 (hemem i x) (a := star a) fun H => ha (hv.hom_inj ?_)
    simpa [hτ, starRingEnd_apply] using H.symm
  have k1 : ∀ w ∈ P.eigW τ, ∀ x, A x = 0 → P.pairV w x = 0 := by
    intro w hw x hx
    obtain ⟨a, ha, haw⟩ := exists_smul_mem_latLie T hε hw.1
    have h1 := (alC_eq_zero_iff T x).1 hx _ haw
    rw [← algebraMap_smul C a, map_smul, LinearMap.smul_apply, smul_eq_mul] at h1
    exact (mul_eq_zero.1 h1).resolve_left fun h0 => ha (hv.hom_inj (by rw [h0, map_zero]))
  have k2 : ∀ x ∈ P.eigV (embO hv ψ), (∀ w ∈ P.eigW τ, P.pairV w x = 0) → A x = 0 := by
    intro x hx H
    refine (alC_eq_zero_iff T x).2 fun w hw => ?_
    have hW := latLie_le_W T hε hw
    rw [← P.iSup_eigW (σ := fun i : E →+* C => embO hv i) sp] at hW
    refine Submodule.iSup_induction _ (motive := fun w => P.pairV w x = 0) hW
      (fun i w hw => ?_) (by simp) (fun a b ha hb => by
        rw [map_add, LinearMap.add_apply, ha, hb, add_zero])
    by_cases hi : embO hv i = τ
    · exact H w (hi ▸ hw)
    · obtain ⟨a, ha⟩ := not_forall.1 fun H => hi (RingHom.ext H)
      exact pairV_eq_zero P hw.2 hx (a := a) fun H => ha (hv.hom_inj H)
  have hAe : ∀ x, A (e ψ x) ∈ eig C (actH D) σ := fun x =>
    alC_mem_eig C D σ (hE1.le (Submodule.mem_map_of_mem (hemem ψ x)))
  have hAr : ∀ x, A x - A (e ψ x) ∈ ⨆ s : {s : ℤ_[p] ⊗[ℤ] 𝓞 E →+* O // s ≠ σ},
      eig C (actH D) s.1 := by
    intro x
    rw [← map_sub, hsplit, map_sum]
    refine Submodule.sum_mem _ fun i hi => ?_
    let s : ℤ_[p] ⊗[ℤ] 𝓞 E →+* O := (Algebra.TensorProduct.lift (algebraMap ℤ_[p] O).toIntAlgHom
      (embO hv i).toIntAlgHom fun _ _ => Commute.all _ _).toRingHom
    have hs : s.comp (Algebra.TensorProduct.includeRight :
        𝓞 E →ₐ[ℤ] ℤ_[p] ⊗[ℤ] 𝓞 E).toRingHom = embO hv i := by
      ext a
      simp [s]
    have hne : s ≠ σ := fun H => Finset.ne_of_mem_erase hi (hinj i ψ fun a => by
      rw [← hs, H, hσ])
    exact Submodule.mem_iSup_of_mem ⟨s, hne⟩
      (alC_mem_eig C D s ((hE s i hs).1.le (Submodule.mem_map_of_mem (hemem i x))))
  have hFil : ∀ m, m ∈ filQuot C D σ ↔
      ∃ t, (∀ w ∈ P.latLie, P.pairV w t ∈ (algebraMap O C).range) ∧ A (e ψ t) = m := by
    intro m
    have hex := (GlobalTheory.T.sandwich_kernel_range_exact p C v O hv ε hε _ h D).1
    constructor
    · rintro ⟨hm, hm'⟩
      obtain ⟨_, ⟨f, hf, rfl⟩, r, hr, hfr⟩ := Submodule.mem_sup.1 hm'
      obtain ⟨u, hu⟩ : incl C h f ∈ LinearMap.range (alC C D) := hex.le (by
        rw [LinearMap.mem_ker, bC_incl, show D.bb f = 0 from hf, map_zero])
      have hA : A (φ.symm u) = incl C h f := by simpa [A] using hu
      refine ⟨φ.symm u, (T.fil _).1 fun i => ⟨f i, (congrFun hA i).symm⟩, ?_⟩
      rw [eq_comm, ← sub_eq_zero]
      refine (Submodule.disjoint_def.1 (disjoint_eigH C D hv.hom_inj σ)) _
        (Submodule.sub_mem _ hm (hAe _)) ?_
      have : m - A (e ψ (φ.symm u)) = r + (A (φ.symm u) - A (e ψ (φ.symm u))) := by
        rw [hA, ← hfr]; abel
      rw [this]
      exact Submodule.add_mem _ hr (hAr _)
    · rintro ⟨t, ht, rfl⟩
      choose f hf using (T.fil t).2 ht
      have hA : incl C h f = A t := funext hf
      have hf0 : f ∈ D.Fil := by
        have h1 : bC C D (A t) = 0 := hex.ge ⟨_, rfl⟩
        rw [← hA, bC_incl] at h1
        exact funext fun i => hv.hom_inj ((congrFun h1 i).trans (map_zero _).symm)
      refine ⟨hAe t, Submodule.mem_sup.2 ⟨_, ⟨f, hf0, rfl⟩, _, Submodule.neg_mem _ (hAr t), ?_⟩⟩
      rw [hA]; abel
  have hAl : ∀ m, m ∈ alQuot C D σ ↔
      ∃ t, (∀ w ∈ P.latT, P.pairV w t ∈ (algebraMap O C).range) ∧ A (e ψ t) = m := by
    intro m
    rw [alQuot, ← hE3]
    constructor
    · rintro ⟨_, ⟨_, ⟨t, ht, rfl⟩, rfl⟩, rfl⟩
      exact ⟨t, (mem_latT_iff_pair P t).1 ht, rfl⟩
    · rintro ⟨t, ht, rfl⟩
      exact ⟨_, ⟨_, ⟨t, (mem_latT_iff_pair P t).2 ht, rfl⟩, rfl⟩, rfl⟩
  have hy' := hy.trans (wRec_eq T hε τ)
  have hyS : ∀ i, y i ∈ P.eigW τ := fun i => (hy'.le (Submodule.subset_span ⟨i, rfl⟩)).2
  haveI : FiniteDimensional C P.V := φ.symm.finiteDimensional
  have hsp : Submodule.span C (Set.range fun i => ∑ j, g' i j • y j) = P.eigW τ := by
    refine Submodule.eq_of_le_of_finrank_eq (Submodule.span_le.2 ?_) ?_
    · rintro _ ⟨i, rfl⟩
      exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (hyS j)
    · rw [finrank_span_eq_card hg.1, hq, Fintype.card_fin]
  have hz : Submodule.span O (Set.range fun i => ∑ j, g' i j • y j) =
      P.latT ⊓ (P.eigW τ).restrictScalars O := by
    rw [hg.2, hsp]
    exact le_antisymm (fun x hx => ⟨hx.1.1, hx.2⟩) fun x hx => ⟨⟨hx.1, hx.2.2⟩, hx.2⟩
  obtain ⟨x₀, hx₀⟩ := exists_dual_family P.pairV (exists_pairV_eq P) _ hg.1
  let x : Fin q → P.V := fun l => e ψ (x₀ l)
  let N : Matrix (Fin q) (Fin q) C := Matrix.of fun i l => P.pairV (y i) (x l)
  have hx : ∀ i l, P.pairV (∑ j, g' i j • y j) (x l) = if i = l then 1 else 0 := fun i l => by
    rw [← hx₀]
    exact heS _ (Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (hyS j)) _
  have hgN : g' * N = 1 := by
    ext i l
    rw [Matrix.one_apply, ← hx, Matrix.mul_apply, map_sum, LinearMap.sum_apply]
    simp only [map_smul, LinearMap.smul_apply, smul_eq_mul, N, Matrix.of_apply]
  have hNg : N * g' = 1 := mul_eq_one_comm.1 hgN
  refine ⟨fun j => A (∑ l, g' l j • x l), Nᵀ, ?_, ?_, ?_⟩
  · refine isBasisOf_dual hv P.pairV (exists_pairV_eq P) (e ψ) A _ _ (hemem ψ) heS k1 k2 _
      (fg_latLie T) (fun w hw => exists_smul_mem_latLie T hε hw.1) y hy' _
      (fun j => Submodule.sum_mem _ fun l _ => Submodule.smul_mem _ _ (hemem ψ _))
      (fun i j => ?_) _ hFil
    rw [← Matrix.one_apply, ← hNg, Matrix.mul_apply, map_sum]
    exact Finset.sum_congr rfl fun l _ => by rw [map_smul, smul_eq_mul, mul_comm]; rfl
  · have e1 : (fun i => ∑ j, Nᵀ i j • A (∑ l, g' l j • x l)) = fun i => A (x i) := by
      funext i
      have e2 : ∀ l, ∑ j, N j i * g' l j = if l = i then 1 else 0 := fun l => by
        rw [← Matrix.one_apply, ← hgN, Matrix.mul_apply]
        simp only [mul_comm]
      simp only [map_sum, map_smul, Finset.smul_sum, smul_smul, Matrix.transpose_apply]
      rw [Finset.sum_comm]
      simp only [← Finset.sum_smul, e2]
      simp
    rw [e1]
    exact isBasisOf_dual hv P.pairV (exists_pairV_eq P) (e ψ) A _ _ (hemem ψ) heS k1 k2 _
      P.fg_latT (fun w _ => P.exists_smul_mem_latT w) _ hz _ (fun j => hemem ψ _) hx _ hAl
  · rw [Matrix.det_transpose, ← Matrix.det_mul, hNg, Matrix.det_one]

end GlobalTheory.DetInv.Duality
