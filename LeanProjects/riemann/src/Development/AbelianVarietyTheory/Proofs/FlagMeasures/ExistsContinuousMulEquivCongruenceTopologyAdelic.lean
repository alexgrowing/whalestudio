import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.ArithmeticCylinders
import Formalism.SharpRestriction.CuspSpanNormBounds.RelevantZeroGramTerms
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ExistsReduction
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.TopfBasis
import Development.AbelianVarietyTheory.Definitions.Foundations.CdScaleTieIff
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FiniteAdelicUnitaryCongruenceTopology
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MemAdelicLatticeClosureIffSwapMemSpan
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CompletedLatticeStabilizerCompactOpen

open MeasureTheory Formalism.MainNotions.S Formalism.BasicNotions Formalism.MainNotions.ArithmeticCylinders GlobalTheory.RowLev NumberField IsDedekindDomain Matrix
open scoped InnerProductSpace ComplexOrder TensorProduct Classical

namespace GlobalTheory.CongTop.Swap

section Abstract

variable {A B : Type} [CommRing A] [CommRing B] {n : Type} [Fintype n] [DecidableEq n]

theorem bc_mem_UJ (φ : A →+* B) {σ : A →+* A} {τ : B →+* B} (h : ∀ x, φ (σ x) = τ (φ x))
    {J : Matrix n n A} {J' : Matrix n n B} (hJ : J.map φ = J') {g : GL n A} (hg : g ∈ Formalism.UG.UJ σ J) :
    Formalism.UG.bc φ g ∈ Formalism.UG.UJ τ J' := by
  have hg' : Formalism.UG.cT σ (g : Matrix n n A) * J * (g : Matrix n n A) = J := hg
  have key : Formalism.UG.cT τ ((g : Matrix n n A).map φ) = (Formalism.UG.cT σ (g : Matrix n n A)).map φ := by
    unfold Formalism.UG.cT
    ext i j
    simp [h]
  subst hJ
  change Formalism.UG.cT τ ((g : Matrix n n A).map φ) * J.map φ * (g : Matrix n n A).map φ = J.map φ
  rw [key, ← Matrix.map_mul, ← Matrix.map_mul, hg']

end Abstract

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes (topTens)
open scoped Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Topology

theorem mem_lamAf_iff {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}
    (L : Submodule (𝓞 E) (Fin n → E)) (y : Fin n → E ⊗[F] Af F) :
    y ∈ lamAf (F := F) L ↔ (fun i => Algebra.TensorProduct.comm F E (Af F) (y i)) ∈
      Formalism.MainNotions.StandardLattice.latHat F E (L : Set (Fin n → E)) := by
  have hcc : ∀ z : E ⊗[F] Af F,
      Algebra.TensorProduct.comm F (Af F) E (Algebra.TensorProduct.comm F E (Af F) z) = z := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul a b => simp
    | add a b ha hb => simp [ha, hb]
  have key := GlobalTheory.AdelicLatticeSwap.mem_latHat_iff_comm_mem_lamAf F E n L
    (fun i => Algebra.TensorProduct.comm F E (Af F) (y i))
  simp only [hcc] at key
  exact key.symm

private theorem tensorComm_sigR_eq_sigR_tensorComm (I : AutInst) (a : I.E ⊗[I.F] Af I.F) :
    Algebra.TensorProduct.comm I.F I.E (Af I.F) (Formalism.UG.sigR I.cm.sig (Af I.F) a) =
      Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (Af I.F) I.cm.sig (Algebra.TensorProduct.comm I.F I.E (Af I.F) a) := by
  induction a using TensorProduct.induction_on with
  | zero => simp
  | tmul x y => simp [Formalism.UG.sigR, Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR]
  | add x y hx hy => simp only [map_add, hx, hy]

private theorem J_map_inclE_comm (I : AutInst) :
    (I.J.map (Formalism.UG.inclE (F := I.F) (Af I.F))).map (Algebra.TensorProduct.comm I.F I.E (Af I.F)) =
      Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.JR (Af I.F) I.J := by
  ext i j
  simp [Formalism.UG.inclE, Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.JR, Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR]

private theorem tensorComm_mulVec_map_eq (I : AutInst) (M : Matrix (Fin I.n) (Fin I.n) (I.E ⊗[I.F] Af I.F))
    (v : Fin I.n → I.E ⊗[I.F] Af I.F) :
    (M.map (Algebra.TensorProduct.comm I.F I.E (Af I.F))) *ᵥ
        (fun i => Algebra.TensorProduct.comm I.F I.E (Af I.F) (v i)) =
      fun i => Algebra.TensorProduct.comm I.F I.E (Af I.F) ((M *ᵥ v) i) := by
  ext i
  simp [Matrix.mulVec, dotProduct, map_sum]

private theorem adLat_hat_eq_latHat (F E : Type) [Field F] [NumberField F] [Field E] [Algebra F E] {m : ℕ}
    (L : Set (Fin m → E)) : GlobalTheory.AdLat.hat F L = Formalism.MainNotions.StandardLattice.latHat F E L := by
  unfold GlobalTheory.AdLat.hat Formalism.MainNotions.StandardLattice.latHat
  congr 1

private theorem stabilizes_lamAf_iff (I : AutInst) (M : Matrix (Fin I.n) (Fin I.n) (I.E ⊗[I.F] Af I.F)) :
    (∀ y, y ∈ lamAf (F := I.F) I.L ↔ M *ᵥ y ∈ lamAf (F := I.F) I.L) ↔
      GlobalTheory.Mem.Vol.StabHat I.F (I.L : Set (Fin I.n → I.E))
        (M.map (Algebra.TensorProduct.comm I.F I.E (Af I.F))) := by
  constructor
  · intro h z
    have h1 := h (fun i => (Algebra.TensorProduct.comm I.F I.E (Af I.F)).symm (z i))
    have e1 : (fun i => Algebra.TensorProduct.comm I.F I.E (Af I.F)
        ((Algebra.TensorProduct.comm I.F I.E (Af I.F)).symm (z i))) = z :=
      funext fun i => AlgEquiv.apply_symm_apply _ _
    have e2 : M.map (Algebra.TensorProduct.comm I.F I.E (Af I.F)) *ᵥ z =
        fun i => Algebra.TensorProduct.comm I.F I.E (Af I.F)
          ((M *ᵥ fun i => (Algebra.TensorProduct.comm I.F I.E (Af I.F)).symm (z i)) i) := by
      rw [← tensorComm_mulVec_map_eq I M]
      congr 1
      exact e1.symm
    rw [mem_lamAf_iff, mem_lamAf_iff, e1, ← e2] at h1
    exact h1
  · intro h y
    rw [mem_lamAf_iff, mem_lamAf_iff, ← tensorComm_mulVec_map_eq I M]
    exact h _

theorem exists_continuousMulEquiv_adelic : ∀ (I : AutInst), ∃ e : I.Gf ≃ₜ* Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.HA (Af I.F) I.cm.sig I.J, (∀ x, ((Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.HA.mat (Af I.F) I.cm.sig I.J (e x) : GL (Fin I.n) _) : Matrix (Fin I.n) (Fin I.n) _) = (I.fmat x).map (Algebra.TensorProduct.comm I.F I.E (Af I.F))) ∧ ∀ x, x ∈ I.Kset ↔ GlobalTheory.Mem.Vol.StabHat I.F (I.L : Set (Fin I.n → I.E)) ((I.fmat x).map (Algebra.TensorProduct.comm I.F I.E (Af I.F))) := by
  intro I
  classical
  obtain ⟨hT2, -, -, -, hKo, ⟨K0, hK0⟩, -⟩ := GlobalTheory.CongTop.adelic_topology I
  have hone : (1 : I.Gf) ∈ I.Kset := by
    have h1 : (1 : I.Gf) ∈ (K0 : Set I.Gf) := K0.one_mem
    rwa [hK0] at h1
  haveI : IsModuleTopology (Af I.F) (Af I.F ⊗[I.F] I.E) := ⟨rfl⟩
  haveI : IsTopologicalRing (Af I.F ⊗[I.F] I.E) := IsModuleTopology.isTopologicalRing (Af I.F) _
  haveI : IsTopologicalGroup (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.HA (Af I.F) I.cm.sig I.J) :=
    inferInstanceAs (IsTopologicalGroup (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.HR (Af I.F) I.cm.sig I.J))
  obtain ⟨KH, hKH, hKHo, hKHc⟩ := GlobalTheory.Mem.Vol.StabGroup.exists_compact_open_stab I.F I.E I.cm.sig I.n I.J I.L
    I.L_fg I.L_span
  let φ : I.E ⊗[I.F] Af I.F →+* Af I.F ⊗[I.F] I.E :=
    (Algebra.TensorProduct.comm I.F I.E (Af I.F)).toRingEquiv.toRingHom
  let ψ : Af I.F ⊗[I.F] I.E →+* I.E ⊗[I.F] Af I.F :=
    (Algebra.TensorProduct.comm I.F I.E (Af I.F)).symm.toRingEquiv.toRingHom
  have hψφ : ∀ a, ψ (φ a) = a := fun a => (Algebra.TensorProduct.comm I.F I.E (Af I.F)).symm_apply_apply a
  have hφψ : ∀ b, φ (ψ b) = b := fun b => (Algebra.TensorProduct.comm I.F I.E (Af I.F)).apply_symm_apply b
  have hsig : ∀ a, φ (Formalism.UG.sigR I.cm.sig (Af I.F) a) =
      Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (Af I.F) I.cm.sig (φ a) := fun a => tensorComm_sigR_eq_sigR_tensorComm I a
  have hsig' : ∀ b, ψ (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (Af I.F) I.cm.sig b) =
      Formalism.UG.sigR I.cm.sig (Af I.F) (ψ b) := by
    intro b
    have h2 := congrArg ψ (hsig (ψ b))
    rw [hψφ, hφψ] at h2
    exact h2.symm
  have hJ : (I.J.map (Formalism.UG.inclE (F := I.F) (Af I.F))).map φ = Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.JR (Af I.F) I.J :=
    J_map_inclE_comm I
  have hJ' : (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.JR (Af I.F) I.J).map ψ = I.J.map (Formalism.UG.inclE (F := I.F) (Af I.F)) := by
    rw [← hJ, Matrix.map_map]
    ext i j
    simp only [Matrix.map_apply, Function.comp_apply, hψφ]
  have hmem : ∀ x : I.Gf, Formalism.UG.bc φ (x : GL (Fin I.n) (I.E ⊗[I.F] Af I.F)) ∈
      Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.HR (Af I.F) I.cm.sig I.J := fun x => bc_mem_UJ φ hsig hJ x.2
  have hmem' : ∀ h : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.HA (Af I.F) I.cm.sig I.J,
      Formalism.UG.bc ψ (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.HA.mat (Af I.F) I.cm.sig I.J h) ∈
        Formalism.UG.UPts I.cm.sig I.J (Af I.F) :=
    fun h => bc_mem_UJ ψ hsig' hJ'
      (Subtype.property (p := fun g => g ∈ Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.HR (Af I.F) I.cm.sig I.J) h)
  have hl : ∀ g : GL (Fin I.n) (I.E ⊗[I.F] Af I.F), Formalism.UG.bc ψ (Formalism.UG.bc φ g) = g := by
    intro g
    ext i j
    simp [Formalism.UG.bc, hψφ]
  have hr : ∀ g : GL (Fin I.n) (Af I.F ⊗[I.F] I.E), Formalism.UG.bc φ (Formalism.UG.bc ψ g) = g := by
    intro g
    ext i j
    simp [Formalism.UG.bc, hφψ]
  let e₀ : I.Gf ≃* Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.HA (Af I.F) I.cm.sig I.J :=
    { toFun := fun x => (⟨Formalism.UG.bc φ (x : GL (Fin I.n) (I.E ⊗[I.F] Af I.F)), hmem x⟩ :
        ↥(Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.HR (Af I.F) I.cm.sig I.J))
      invFun := fun h => ⟨Formalism.UG.bc ψ (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.HA.mat (Af I.F) I.cm.sig I.J h), hmem' h⟩
      left_inv := fun x => Subtype.ext (hl (x : GL (Fin I.n) (I.E ⊗[I.F] Af I.F)))
      right_inv := fun h => Subtype.ext (hr (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.HA.mat (Af I.F) I.cm.sig I.J h))
      map_mul' := fun x y => Subtype.ext (map_mul (Formalism.UG.bc φ) (x : GL (Fin I.n) (I.E ⊗[I.F] Af I.F))
        (y : GL (Fin I.n) (I.E ⊗[I.F] Af I.F))) }
  have hK : ∀ x : I.Gf, x ∈ I.Kset ↔ GlobalTheory.Mem.Vol.StabHat I.F (I.L : Set (Fin I.n → I.E))
      ((I.fmat x).map (Algebra.TensorProduct.comm I.F I.E (Af I.F))) := fun x => stabilizes_lamAf_iff I (I.fmat x)
  have hKe : ∀ x : I.Gf, x ∈ I.Kset ↔ e₀ x ∈ KH := fun x => (hK x).trans (hKH (e₀ x)).symm
  have hmat : ∀ x : I.Gf, ((Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.HA.mat (Af I.F) I.cm.sig I.J (e₀ x) :
      GL (Fin I.n) (Af I.F ⊗[I.F] I.E)) : Matrix (Fin I.n) (Fin I.n) (Af I.F ⊗[I.F] I.E)) =
      (I.fmat x).map (Algebra.TensorProduct.comm I.F I.E (Af I.F)) := fun x => rfl
  have hcont_inv : Continuous (e₀.symm : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.HA (Af I.F) I.cm.sig I.J → I.Gf) := by
    apply continuous_of_continuousAt_one e₀.symm
    rw [ContinuousAt, Filter.tendsto_def]
    intro W hW
    simp only [map_one] at hW
    obtain ⟨g, hg1, hgW⟩ := I.topf_basis W hW
    have hN := GlobalTheory.Mem.Vol.StabGroup.congr_mem_nhds I.F I.E I.n I.L I.L_fg I.L_span g hg1
    have hmatc : Continuous (fun h : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.HA (Af I.F) I.cm.sig I.J =>
        ((Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.HA.mat (Af I.F) I.cm.sig I.J h : GL (Fin I.n) (Af I.F ⊗[I.F] I.E)) :
          Matrix (Fin I.n) (Fin I.n) (Af I.F ⊗[I.F] I.E))) :=
      Units.continuous_val.comp continuous_subtype_val
    have h1 := hmatc.continuousAt (x := 1) |>.preimage_mem_nhds hN
    filter_upwards [h1, hKHo.mem_nhds KH.one_mem] with h hh hk
    apply hgW
    have hx : (I.fmat (e₀.symm h)).map (Algebra.TensorProduct.comm I.F I.E (Af I.F)) =
        ((Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.HA.mat (Af I.F) I.cm.sig I.J h : GL (Fin I.n) (Af I.F ⊗[I.F] I.E)) :
          Matrix (Fin I.n) (Fin I.n) (Af I.F ⊗[I.F] I.E)) := by
      rw [← hmat, MulEquiv.apply_symm_apply]
    refine ⟨(hK (e₀.symm h)).2 (hx ▸ (hKH h).1 hk), ?_⟩
    intro y hy
    have hy' := (mem_lamAf_iff I.L y).1 hy
    rw [← adLat_hat_eq_latHat] at hy'
    obtain ⟨w, hw, hwe⟩ := hh _ hy'
    refine ⟨fun i => (Algebra.TensorProduct.comm I.F I.E (Af I.F)).symm (w i), ?_, ?_⟩
    · rw [mem_lamAf_iff]
      have e1 : (fun i => Algebra.TensorProduct.comm I.F I.E (Af I.F)
          ((Algebra.TensorProduct.comm I.F I.E (Af I.F)).symm (w i))) = w :=
        funext fun i => AlgEquiv.apply_symm_apply _ _
      rw [e1, ← adLat_hat_eq_latHat]
      exact hw
    · funext i
      apply (Algebra.TensorProduct.comm I.F I.E (Af I.F)).injective
      have e3 := congrFun hwe i
      beta_reduce at e3
      rw [← hx, tensorComm_mulVec_map_eq] at e3
      simp only [Pi.sub_apply, Pi.smul_apply, nsmul_eq_mul] at e3
      simp only [Matrix.sub_mulVec, Matrix.one_mulVec, Pi.sub_apply, Pi.smul_apply, map_sub, smul_eq_mul,
        map_mul, map_natCast, AlgEquiv.apply_symm_apply, e3]
  have hcont : Continuous (e₀ : I.Gf → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.HA (Af I.F) I.cm.sig I.J) := by
    apply continuous_of_continuousAt_one e₀
    rw [ContinuousAt, Filter.tendsto_def]
    intro V hV
    simp only [map_one] at hV
    obtain ⟨V', hV'V, hV'o, hV'1⟩ := mem_nhds_iff.1 hV
    have hC : IsCompact ((KH : Set (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.HA (Af I.F) I.cm.sig I.J)) \ V') := hKHc.diff hV'o
    have hCi : IsClosed (e₀.symm '' ((KH : Set (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.HA (Af I.F) I.cm.sig I.J)) \ V')) :=
      (hC.image hcont_inv).isClosed
    have hO : IsOpen (I.Kset ∩ (e₀.symm '' ((KH : Set (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.HA (Af I.F) I.cm.sig I.J)) \ V'))ᶜ) :=
      hKo.inter hCi.isOpen_compl
    have h1O : (1 : I.Gf) ∈ I.Kset ∩ (e₀.symm '' ((KH : Set (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.HA (Af I.F) I.cm.sig I.J)) \ V'))ᶜ := by
      refine ⟨hone, ?_⟩
      rintro ⟨c, ⟨-, hcV⟩, hc1⟩
      apply hcV
      have hc : c = 1 := by simpa using congrArg e₀ hc1
      rw [hc]
      exact hV'1
    refine Filter.mem_of_superset (hO.mem_nhds h1O) ?_
    rintro x ⟨hxK, hxC⟩
    show e₀ x ∈ V
    apply hV'V
    by_contra hxV
    exact hxC ⟨e₀ x, ⟨(hKe x).1 hxK, hxV⟩, e₀.symm_apply_apply x⟩
  exact ⟨{ toMulEquiv := e₀, continuous_toFun := hcont, continuous_invFun := hcont_inv },
    fun x => rfl, hK⟩

end GlobalTheory.CongTop.Swap
