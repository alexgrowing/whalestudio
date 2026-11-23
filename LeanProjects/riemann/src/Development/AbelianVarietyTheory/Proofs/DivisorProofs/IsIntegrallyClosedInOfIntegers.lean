import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.LieInj
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ScholzeWeinsteinB
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.EpsilonPairingZeta
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.HodgeTateKernel
import Development.AbelianVarietyTheory.Definitions.Divisors.TorsionTowersOfDivisibleGroup
import Development.AbelianVarietyTheory.Definitions.Divisors.IsLatBasisHtLatIffSpanEq

open GlobalTheory GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps GlobalTheory.DetInv GlobalTheory.HTLat GlobalTheory.CompHt GlobalTheory.PDivGroup Matrix TensorProduct NumberField CategoryTheory

namespace GlobalTheory.PointGroup

theorem isIntegrallyClosedIn_of_integers {C : Type} [Field C] {v : Valuation C NNReal} {O : Type}
    [CommRing O] [Algebra O C] (hv : v.Integers O) : IsIntegrallyClosedIn O C :=
  isIntegrallyClosedIn_iff.2 ⟨hv.hom_inj, fun h => hv.exists_of_le_one
    (hv.isIntegral_iff_v_le_one.1 h)⟩

theorem exists_tensor_eq {R O M N : Type} [CommRing R] [CommRing O] [Algebra R O] [AddCommGroup M]
    [Module R M] [AddCommGroup N] [Module R N] [Module.Finite R N] [Module.Free R N]
    (B : M →ₗ[R] N →ₗ[R] R) (hB : Function.Surjective B) (φ : O ⊗[R] N →ₗ[O] O) :
    ∃ x : O ⊗[R] M, ∀ n, TensorProduct.rid R O ((B.flip n).baseChange O x) = φ (1 ⊗ₜ n) := by
  let b := Module.Free.chooseBasis R N
  choose s hs using fun i => hB (b.coord i)
  refine ⟨∑ i, φ (1 ⊗ₜ b i) ⊗ₜ s i, fun n => ?_⟩
  conv_rhs => rw [← b.sum_repr n]
  simp only [map_sum, LinearMap.baseChange_tmul, LinearMap.flip_apply, hs, TensorProduct.rid_tmul,
    TensorProduct.tmul_sum, Module.Basis.coord_apply, TensorProduct.tmul_smul]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← algebraMap_smul O (b.repr n i) ((1 : O) ⊗ₜ[R] b i), map_smul, algebraMap_smul]

theorem exists_lift {R Λ E : Type} [CommRing R] [CommRing Λ] [Ring E] [Algebra R E]
    (ψ : Λ →+* E) : ∃ ρ : R ⊗[ℤ] Λ →+* E, ∀ a, ρ (1 ⊗ₜ a) = ψ a :=
  ⟨(Algebra.TensorProduct.lift (algebraMap R E).toIntAlgHom ψ.toIntAlgHom
    fun a b => Algebra.commute_algebraMap_left a _).toRingHom, fun a => (Algebra.TensorProduct.lift_tmul _ _ _ 1 a).trans
      (by rw [map_one, one_mul]; rfl)⟩

variable {p : ℕ} [Fact p.Prime] {C : Type} [Field C] [IsAlgClosed C] [CharZero C]
  {v : Valuation C NNReal} {O : Type} [CommRing O] [Algebra O C]

theorem exists_form (hv : v.Integers O) (G : PDivGroup p O) (ζ : (PDivGroup.mu p O).Tate)
    (hζ : Function.Bijective fun a : ℤ_[p] => a • ζ) :
    ∃ B : G.Tate →ₗ[ℤ_[p]] G.dual.Tate →ₗ[ℤ_[p]] ℤ_[p], (∀ s χ, pairing G O s χ = B s χ • ζ) ∧
      Function.Bijective B ∧ Function.Bijective B.flip := by
  haveI := isIntegrallyClosedIn_of_integers hv
  let z := LinearEquiv.ofBijective (LinearMap.toSpanSingleton ℤ_[p] _ ζ) hζ
  refine ⟨(pairing G O).compr₂ z.symm.toLinearMap, fun s χ => (z.apply_symm_apply _).symm, ?_, ?_⟩
  · exact (LinearEquiv.congrRight (M := G.dual.Tate) z.symm).bijective.comp (G.pairing_bijective C)
  · exact (LinearEquiv.congrRight (M := G.Tate) z.symm).bijective.comp (G.pairing_flip_bijective C)

theorem finite_tate (hv : v.Integers O) (G : PDivGroup p O) : Module.Finite ℤ_[p] G.Tate :=
  haveI := isIntegrallyClosedIn_of_integers hv
  G.finite_tate C

theorem free_tate (hv : v.Integers O) (G : PDivGroup p O) : Module.Free ℤ_[p] G.Tate :=
  haveI := isIntegrallyClosedIn_of_integers hv
  G.free_tate C

variable [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O]
  {ε : PreTilt O p} {hε : GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta.IsPrimitiveSystem ε}

theorem lie_eq_zero (hv : v.Integers O) (H : GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta.HodgeTateSandwichAt hε)
    (G : PDivGroup p O) (y : G.Lie) (hy : ∀ χ, y (dlog G χ) = 0) : y = 0 := by
  obtain ⟨u₁, u₂, H⟩ := H
  obtain ⟨D, e, fil, lie, R⟩ := H G ℤ_[p] G.padicAction
  obtain ⟨B, hB, -, hB'⟩ := exists_form hv G _ (GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta.epsEquiv hε).bijective
  have hE : ∀ s χ, GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta.epsPairing hε G s χ = B s χ := fun s χ =>
    (LinearEquiv.symm_apply_eq _).2 (hB s χ)
  have h0 : GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta.bQuot D (lie.symm y) = 0 := by
    funext j
    obtain ⟨χ, hχ⟩ := hB'.2 (LinearMap.proj j ∘ₗ e.toLinearMap)
    have h1 : ∀ s, B s χ = e s j := fun s => LinearMap.congr_fun hχ s
    have h := R.b_eq y χ
    rw [← dlog_eq_omegaMap, hy, mul_zero, GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta.pairingO] at h
    simpa [hE, h1, Pi.single_apply, apply_ite] using h
  have h1 : lie.symm y = 0 := by
    have hk : LinearMap.ker (GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta.bQuot D) = ⊥ := Submodule.ker_liftQ_eq_bot _ _ _ le_rfl
    exact LinearMap.ker_eq_bot'.1 hk _ h0
  exact lie.symm.map_eq_zero_iff.1 h1

theorem omega_eq_zero (H : GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta.HodgeTateSandwichAt hε)
    (G : PDivGroup p O) (w : G.omega) (hw : ∀ y : G.Lie, y w = 0) : w = 0 := by
  obtain ⟨u₁, u₂, H⟩ := H
  obtain ⟨D, e, fil, lie, R⟩ := H G.dual ℤ_[p] G.dual.padicAction
  have h : fil (omegaMap _ _ G.bidual.inv w) = 0 := Subtype.ext (funext fun j =>
    hw (LinearMap.proj j ∘ₗ D.Fil.subtype ∘ₗ fil.toLinearMap ∘ₗ omegaMap _ _ G.bidual.inv))
  have h2 := congrArg (omegaMap _ _ G.bidual.hom) (fil.map_eq_zero_iff.1 h)
  rwa [map_zero, ← LinearMap.comp_apply, ← omegaMap_comp, Iso.hom_inv_id, omegaMap_id] at h2

omit [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O] in

theorem hodgeTateLinear_dual_eq_zero_iff [Algebra ℤ_[p] O] (G : PDivGroup p O)
    (z : O ⊗[ℤ_[p]] G.dual.Tate) : G.dual.hodgeTateLinear z = 0 ↔ dlogLinear G z = 0 := by
  have h : G.dual.hodgeTateLinear z = omegaMap _ _ G.bidual.inv (dlogLinear G z) := by
    induction z using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => simp only [map_add, hx, hy]
    | tmul c χ =>
      rw [hodgeTateLinear_tmul, dlogLinear_tmul, map_smul, hodgeTate_apply, ← dlog_tateMap,
        dualHom_bidual_inv]
  rw [h]
  refine ⟨fun h0 => ?_, fun h0 => by rw [h0, map_zero]⟩
  have h2 := congrArg (omegaMap _ _ G.bidual.hom) h0
  rwa [map_zero, ← LinearMap.comp_apply, ← omegaMap_comp, Iso.hom_inv_id, omegaMap_id] at h2

omit [IsAlgClosed C] [CharZero C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O] in

def KerIsLie [Algebra ℤ_[p] O] (G : PDivGroup p O)
    (B : G.Tate →ₗ[ℤ_[p]] G.dual.Tate →ₗ[ℤ_[p]] ℤ_[p]) : Prop :=
  ∀ x : O ⊗[ℤ_[p]] G.Tate, G.hodgeTateLinear x = 0 ↔ ∃ (c : O) (y : G.Lie), c ≠ 0 ∧
    ∀ χ, c * (TensorProduct.rid ℤ_[p] O) ((B.flip χ).baseChange O x) = y (dlog G χ)

variable [Algebra ℤ_[p] O]

omit [IsDomain O] in

theorem eq_id_of_tateMap (SW : GlobalTheory.Published.ScholzeWeinsteinB) (hv : v.Integers O) {G : PDivGroup p O}
    (φ : G ⟶ G) (h : ∀ t, tateMap G G O φ t = t) : φ = 𝟙 G :=
  ((SW p C v O hv).1 G G LinearMap.id fun x hx => by rwa [LinearMap.baseChange_id]).unique
    (LinearMap.ext h) rfl

omit [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] in

theorem exists_ker_of_lie (hv : v.Integers O) {G : PDivGroup p O}
    {B : G.Tate →ₗ[ℤ_[p]] G.dual.Tate →ₗ[ℤ_[p]] ℤ_[p]} (hB : Function.Surjective B)
    (hk : KerIsLie G B) (y : G.Lie) : ∃ x, G.hodgeTateLinear x = 0 ∧
      ∀ χ, (TensorProduct.rid ℤ_[p] O) ((B.flip χ).baseChange O x) = y (dlog G χ) := by
  haveI := finite_tate hv G.dual
  haveI := free_tate hv G.dual
  obtain ⟨x, hx⟩ := exists_tensor_eq B hB (y ∘ₗ dlogLinear G)
  have hx' : ∀ χ, (TensorProduct.rid ℤ_[p] O) ((B.flip χ).baseChange O x) = y (dlog G χ) :=
    fun χ => by rw [hx, LinearMap.comp_apply, dlogLinear_tmul, one_smul]
  exact ⟨x, (hk x).2 ⟨1, y, one_ne_zero, fun χ => by rw [one_mul, hx']⟩, hx'⟩

theorem exists_pol (SW : GlobalTheory.Published.ScholzeWeinsteinB) (hv : v.Integers O)
    (H : GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta.HodgeTateSandwichAt hε) (G : PDivGroup p O) (ζ : (PDivGroup.mu p O).Tate)
    (B : G.Tate →ₗ[ℤ_[p]] G.dual.Tate →ₗ[ℤ_[p]] ℤ_[p]) (hB : ∀ s χ, pairing G O s χ = B s χ • ζ)
    (hB1 : Function.Surjective B) (hB2 : Function.Bijective B.flip) (hk : KerIsLie G B)
    (β : LinearMap.BilinForm ℤ_[p] G.Tate) (hβ : Function.Bijective β.flip)
    (hL : ∀ z, G.hodgeTateLinear z = 0 ↔
      ∀ x, G.hodgeTateLinear x = 0 → β.baseChange O x z = 0) :
    ∃ pol : G ≅ G.dual, ∀ s t, pairing G O s (tateMap G G.dual O pol.hom t) = β s t • ζ := by
  let f : G.Tate ≃ₗ[ℤ_[p]] G.dual.Tate :=
    (LinearEquiv.ofBijective β.flip hβ).trans (LinearEquiv.ofBijective B.flip hB2).symm
  have hf : ∀ s t, B s (f t) = β s t := fun s t =>
    LinearMap.congr_fun ((LinearEquiv.ofBijective B.flip hB2).apply_symm_apply (β.flip t)) s
  have h1 : ∀ x (d : O) t, β.baseChange O x (d ⊗ₜ t) =
      d * (TensorProduct.rid ℤ_[p] O) ((B.flip (f t)).baseChange O x) := fun x d t => by
    induction x using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => simp only [map_add, LinearMap.add_apply, hx, hy, mul_add]
    | tmul a s =>
      rw [LinearMap.BilinForm.baseChange_tmul, LinearMap.baseChange_tmul, LinearMap.flip_apply, hf,
        TensorProduct.rid_tmul, mul_smul_comm, mul_comm]
  have h2 : ∀ x (c : O) (y : G.Lie),
      (∀ χ, c * (TensorProduct.rid ℤ_[p] O) ((B.flip χ).baseChange O x) = y (dlog G χ)) →
      ∀ z, c * β.baseChange O x z = y (dlogLinear G (f.toLinearMap.baseChange O z)) :=
    fun x c y h z => by
      induction z using TensorProduct.induction_on with
      | zero => simp
      | add z w hz hw => simp only [map_add, hz, hw, mul_add]
      | tmul d t =>
        rw [h1, LinearMap.baseChange_tmul, dlogLinear_tmul, map_smul, ← h, smul_eq_mul,
          mul_left_comm]
        rfl
  have h3 : ∀ z, G.hodgeTateLinear z = 0 ↔
      G.dual.hodgeTateLinear (f.toLinearMap.baseChange O z) = 0 := fun z => by
    rw [hodgeTateLinear_dual_eq_zero_iff]
    refine ⟨fun hz => omega_eq_zero H G _ fun y => ?_, fun hz => (hL z).2 fun x hx => ?_⟩
    · obtain ⟨x, hx, hx'⟩ := exists_ker_of_lie hv hB1 hk y
      rw [← h2 x 1 y (fun χ => by rw [one_mul, hx']), (hL z).1 hz x hx, mul_zero]
    · obtain ⟨c, y, hc, h⟩ := (hk x).1 hx
      have := h2 x c y h z
      rw [hz, map_zero] at this
      exact (mul_eq_zero.1 this).resolve_left hc
  obtain ⟨φ, hφ, -⟩ := (SW p C v O hv).1 G G.dual f.toLinearMap fun x hx => (h3 x).1 hx
  obtain ⟨ψ, hψ, -⟩ := (SW p C v O hv).1 G.dual G f.symm.toLinearMap fun x hx => (h3 _).2 (by
    rwa [← LinearMap.comp_apply (f.toLinearMap.baseChange O), ← LinearMap.baseChange_comp,
      LinearEquiv.comp_symm, LinearMap.baseChange_id])
  refine ⟨⟨φ, ψ, eq_id_of_tateMap SW hv _ fun t => ?_, eq_id_of_tateMap SW hv _ fun t => ?_⟩,
    fun s t => ?_⟩
  · rw [tateMap_comp, hφ, hψ]; exact f.symm_apply_apply t
  · rw [tateMap_comp, hφ, hψ]; exact f.apply_symm_apply t
  · rw [hφ, hB, ← hf]; rfl

theorem exists_lie_bijective (SW : GlobalTheory.Published.ScholzeWeinsteinB) (hv : v.Integers O)
    (H : GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta.HodgeTateSandwichAt hε) (G G₁ : PDivGroup p O)
    (ζ : (PDivGroup.mu p O).Tate) (hζ : Function.Injective fun a : ℤ_[p] => a • ζ)
    (B : G.Tate →ₗ[ℤ_[p]] G.dual.Tate →ₗ[ℤ_[p]] ℤ_[p]) (hB : ∀ s χ, pairing G O s χ = B s χ • ζ)
    (hB1 : Function.Surjective B) (hk : KerIsLie G B)
    (ι : G₁.Tate →ₗ[ℤ_[p]] G.Tate) (r : G.Tate →ₗ[ℤ_[p]] G₁.Tate) (hr : ∀ s, r (ι s) = s)
    (h1 : ∀ x, G₁.hodgeTateLinear x = 0 ↔ G.hodgeTateLinear (ι.baseChange O x) = 0)
    (h2 : ∀ x, G.hodgeTateLinear x = 0 → ι.baseChange O (r.baseChange O x) = x) :
    ∃ i : G₁ ⟶ G, tateMap G₁ G O i = ι ∧ Function.Bijective (lieMap G₁ G i) := by
  obtain ⟨i, hi, -⟩ := (SW p C v O hv).1 G₁ G ι fun x hx => (h1 x).1 hx
  obtain ⟨ρ, hρ, -⟩ := (SW p C v O hv).1 G G₁ r fun x hx => (h1 _).2 (by rwa [h2 x hx])
  have h3 : i ≫ ρ = 𝟙 G₁ := eq_id_of_tateMap SW hv _ fun t => by rw [tateMap_comp, hi, hρ, hr]
  refine ⟨i, hi, Function.bijective_iff_has_inverse.2 ⟨lieMap G G₁ ρ, fun y => ?_, fun y => ?_⟩⟩
  · rw [← LinearMap.comp_apply, ← lieMap_comp, h3, lieMap_id, LinearMap.id_apply]
  · rw [← LinearMap.comp_apply, ← lieMap_comp]
    obtain ⟨x, hx, hx'⟩ := exists_ker_of_lie hv hB1 hk y
    refine sub_eq_zero.1 (lie_eq_zero hv H G _ fun χ => ?_)
    have h4 : B.flip (tateMap _ _ O (dualHom G G (ρ ≫ i)) χ) = B.flip χ ∘ₗ ι ∘ₗ r :=
      LinearMap.ext fun s => hζ (by
        have := pairing_tateMap (ρ ≫ i) s χ
        rw [hB, hB, tateMap_comp, hi, hρ] at this
        exact this.symm)
    rw [LinearMap.sub_apply, lieMap_apply, ← dlog_tateMap, ← hx', ← hx', h4,
      LinearMap.baseChange_comp, LinearMap.baseChange_comp, LinearMap.comp_apply,
      LinearMap.comp_apply, h2 x hx, sub_self]

omit [IsDomain O] in

theorem exists_action (SW : GlobalTheory.Published.ScholzeWeinsteinB) (hv : v.Integers O) (G : PDivGroup p O)
    {Λ : Type} [CommRing Λ] (α : Λ →+* Module.End ℤ_[p] G.Tate)
    (h : ∀ a x, G.hodgeTateLinear x = 0 → G.hodgeTateLinear ((α a).baseChange O x) = 0) :
    ∃ ρ : Action (ℤ_[p] ⊗[ℤ] Λ) G, ∀ a, ρ.onTate O (1 ⊗ₜ a) = α a := by
  have hex := fun a => (SW p C v O hv).1 G G (α a) (h a)
  choose φ hφ hu using hex
  let ψ : Λ →+* End G :=
    { toFun := φ
      map_one' := (hu 1 _ (by rw [map_one]; rfl)).symm
      map_mul' := fun a b => (hu (a * b) (φ b ≫ φ a) (by
        rw [map_mul, ← hφ a, ← hφ b]; rfl)).symm
      map_zero' := (hu 0 _ (by rw [map_zero]; exact map_zero _)).symm
      map_add' := fun a b => (hu (a + b) (φ a + φ b) (by
        rw [map_add, ← hφ a, ← hφ b]; exact map_add _ _ _)).symm }
  obtain ⟨ρ, hρ⟩ := exists_lift (R := ℤ_[p]) ψ
  exact ⟨ρ, fun a => by rw [Action.onTate_apply, hρ]; exact hφ a⟩

end GlobalTheory.PointGroup
