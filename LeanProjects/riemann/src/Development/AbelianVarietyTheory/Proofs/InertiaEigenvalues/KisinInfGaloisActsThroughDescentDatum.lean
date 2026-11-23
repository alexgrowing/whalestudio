import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsPotential
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.OneSubPhiOntoOfFilZero
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BhattScholzeCrystallineLattices
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.ConductorExponents
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinLatticeExponentsAinfComparisonStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TeichmullerSubOneAinfPropertiesCompatibleRootsStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

noncomputable section

namespace GlobalTheory.TameAct

variable {l : ℕ} [hl : Fact l.Prime] {a e : ℕ} [NeZero a] [NeZero e]
  {O K : Type} [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O]
  [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K]
  [TameDescentExponentData K l e a] (t : Wq l a →ₐ[ℤ_[l]] O) (ϖ : PiSys l e)

variable (O) in

def actS (γ : TameGal K l e a) : (ZMod a → S O K e) →+* (ZMod a → S O K e) where
  toFun f τ := ⟨ringAct γ (fun σ => (f σ : K⟦X⟧)) τ, rot_S.ringAct_mem γ (fun σ => (f σ).2) τ⟩
  map_one' := funext fun τ => Subtype.ext (by
    change ringAct γ (fun _ => (1 : K⟦X⟧)) τ = 1
    rw [show (fun _ : ZMod a => (1 : K⟦X⟧)) = 1 from rfl, map_one]; rfl)
  map_mul' f g := funext fun τ => Subtype.ext (by
    change ringAct γ (fun σ => (f σ : K⟦X⟧) * g σ) τ =
      ringAct γ (fun σ => (f σ : K⟦X⟧)) τ * ringAct γ (fun σ => (g σ : K⟦X⟧)) τ
    rw [show (fun σ => (f σ : K⟦X⟧) * g σ) = (fun σ => (f σ : K⟦X⟧)) * (fun σ => (g σ : K⟦X⟧)) from rfl,
      map_mul]; rfl)
  map_zero' := funext fun τ => Subtype.ext (by
    change ringAct γ (fun _ => (0 : K⟦X⟧)) τ = 0
    rw [show (fun _ : ZMod a => (0 : K⟦X⟧)) = 0 from rfl, map_zero]; rfl)
  map_add' f g := funext fun τ => Subtype.ext (by
    change ringAct γ (fun σ => (f σ : K⟦X⟧) + g σ) τ =
      ringAct γ (fun σ => (f σ : K⟦X⟧)) τ + ringAct γ (fun σ => (g σ : K⟦X⟧)) τ
    rw [show (fun σ => (f σ : K⟦X⟧) + g σ) = (fun σ => (f σ : K⟦X⟧)) + (fun σ => (g σ : K⟦X⟧)) from rfl,
      map_add]; rfl)

theorem coe_actS (γ : TameGal K l e a) (f : ZMod a → S O K e) (τ : ZMod a) :
    (actS O γ f τ : K⟦X⟧) = ringAct γ (fun σ => (f σ : K⟦X⟧)) τ := rfl

theorem galOCr_iC_of_covers {h : GQ l} {γ : TameGal K l e a} (hc : Covers K t ϖ h γ) (f : ZMod a → S O K e) :
    galOCr O h (ϖ.iC t K f) = ϖ.iC t K (actS O γ f) := by
  let F : (ZMod a → S O K e) →+* OCr l O := (galOCr O h).toRingHom.comp (ϖ.iC t K).toRingHom
  let F' : (ZMod a → S O K e) →+* OCr l O := (ϖ.iC t K).toRingHom.comp (actS O γ)
  have hA : ∀ f : ZMod a → A O K, F (fun τ => ⟨f τ, A_le_S l e (f τ).2⟩) =
      F' (fun τ => ⟨f τ, A_le_S l e (f τ).2⟩) := by
    intro f
    let f' : ZMod a → A O K := fun τ =>
      ⟨ringAct γ (fun σ => (f σ : K⟦X⟧)) τ, rot_A.ringAct_mem γ (fun σ => (f σ).2) τ⟩
    have h1 : actS O γ (fun τ => ⟨f τ, A_le_S l e (f τ).2⟩) = fun τ => ⟨f' τ, A_le_S l e (f' τ).2⟩ := rfl
    change galOCr O h (ϖ.iC t K _) = ϖ.iC t K (actS O γ _)
    rw [h1, ϖ.iC_of_mem t K, ϖ.iC_of_mem t K, galOCr_toOCr, hc f f' (fun τ => rfl)]
  let d : S O K e →+* (ZMod a → S O K e) := Pi.ringHom fun _ => RingHom.id _
  have hd : F.comp d = F'.comp d :=
    ringHom_ext_S (O := O) (K := K) l e (fun _ => nat_cancel_OCr hl.out.ne_zero) sep_OCr _ _ fun x => hA fun _ => x
  have hs : ∀ τ : ZMod a, F (Pi.single τ (1 : S O K e)) = F' (Pi.single τ (1 : S O K e)) := fun τ => by
    have e1 : (fun σ => ⟨(((Pi.single τ (1 : A O K) : ZMod a → A O K) σ : A O K) : K⟦X⟧),
        A_le_S l e ((Pi.single τ (1 : A O K) : ZMod a → A O K) σ).2⟩ :
        ZMod a → S O K e) = Pi.single τ (1 : S O K e) := funext fun σ => Subtype.ext (by
      by_cases hσ : σ = τ
      · subst hσ; simp
      · simp [Pi.single_apply, hσ])
    have := hA (Pi.single τ (1 : A O K))
    rwa [e1] at this
  have hx : f = ∑ τ, Pi.single τ (1 : S O K e) * d (f τ) := by
    ext1 σ
    rw [Finset.sum_apply, Finset.sum_eq_single σ (fun τ _ hτ => by simp [d, Pi.single_apply, Ne.symm hτ])
      (by simp)]
    simp only [Pi.mul_apply, Pi.single_eq_same, one_mul]
    rfl
  change F f = F' f
  rw [hx, map_sum, map_sum]
  refine Finset.sum_congr rfl fun τ _ => ?_
  rw [map_mul, map_mul, hs, ← RingHom.comp_apply F d, hd]
  rfl

end GlobalTheory.TameAct

end

namespace GlobalTheory.TameAct

variable {l : ℕ} [hl : Fact l.Prime] {a e : ℕ} [NeZero a] [NeZero e]
  {O K : Type} [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O]
  [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K]
  [TameDescentExponentData K l e a] (t : Wq l a →ₐ[ℤ_[l]] O) (ϖ : PiSys l e)

omit [TameDescentExponentData K l e a] in

theorem pow_mul_iB (N : ℕ) (F : ZMod a → invL l (S O K e)) (G : ZMod a → S O K e)
    (hG : ∀ τ, (G τ : K⟦X⟧) = (l : K⟦X⟧) ^ N * F τ) :
    (l : OB l O) ^ N * ϖ.iB t K F = toOB l O (ϖ.iC t K G) := by
  have h1 : (fun τ => ⟨(G τ : K⟦X⟧), le_away _ _ (G τ).2⟩ : ZMod a → invL l (S O K e)) =
      (l : ZMod a → invL l (S O K e)) ^ N * F := funext fun τ => Subtype.ext (by
    rw [hG τ]
    simp)
  rw [← ϖ.iB_of_mem t K, h1, map_mul, map_pow, map_natCast]

theorem galOB_iB_of_covers {h : GQ l} {γ : TameGal K l e a} (hc : Covers K t ϖ h γ)
    (f f' : ZMod a → invL l (S O K e)) (hf : ∀ τ, (f' τ : K⟦X⟧) = ringAct γ (fun σ => (f σ : K⟦X⟧)) τ) :
    galOB O h (ϖ.iB t K f) = ϖ.iB t K f' := by
  choose n hn using fun τ => mem_away.1 (f τ).2
  set N := ∑ τ, n τ
  have hN : ∀ τ, (l : K⟦X⟧) ^ N * (f τ : K⟦X⟧) ∈ S O K e := fun τ => by
    obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le'
      (Finset.single_le_sum (f := n) (fun _ _ => Nat.zero_le _) (Finset.mem_univ τ))
    rw [show N = k + n τ from hk, pow_add, mul_assoc]
    refine mul_mem (pow_mem (natCast_mem _ l) _) ?_
    simpa using hn τ
  let g : ZMod a → S O K e := fun τ => ⟨_, hN τ⟩
  have h1 := pow_mul_iB t ϖ N f g fun τ => rfl
  have h2 := pow_mul_iB t ϖ N f' (actS O γ g) fun τ => by
    rw [coe_actS]
    have e1 : (fun σ => ((g σ : S O K e) : K⟦X⟧)) = (l : ZMod a → K⟦X⟧) ^ N * fun σ => (f σ : K⟦X⟧) := rfl
    rw [e1, map_mul, map_pow, map_natCast, Pi.mul_apply, Pi.pow_apply, Pi.natCast_apply, hf τ]
  refine (isUnit_l_OB.pow N).mul_left_cancel ?_
  rw [h2, ← galOCr_iC_of_covers t ϖ hc, ← galOB_toOB, ← h1, map_mul, map_pow, map_natCast]

end GlobalTheory.TameAct

namespace GlobalTheory.TameAct

variable {l : ℕ} [hl : Fact l.Prime] {a e : ℕ} [NeZero a] [NeZero e]
  {O K : Type} [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O]
  [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K]
  [TameDescentExponentData K l e a] {t : Wq l a →ₐ[ℤ_[l]] O} {ϖ : PiSys l e}

section Tensor

variable {G : Type} [Group G] [TopologicalSpace G]

theorem TWact_smul {R : Type} [CommRing R] [Algebra O R] (f : R →ₐ[O] R) (T : LocLat G ℚ_[l] K O) (g : G)
    (r : R) (x : TW R T) : TWact f T g (r • x) = f r • TWact f T g x := by
  induction x using TensorProduct.induction_on with
  | zero => simp only [smul_zero, map_zero]
  | tmul w y =>
    simp only [TWact, smul_tmul', TensorProduct.map_tmul, AlgHom.toLinearMap_apply, smul_eq_mul, map_mul]
  | add x y hx hy => simp only [smul_add, map_add, hx, hy]

theorem TWact_TWincl {R R' : Type} [CommRing R] [CommRing R'] [Algebra O R] [Algebra O R'] (φ : R →ₐ[O] R')
    (f : R →ₐ[O] R) (f' : R' →ₐ[O] R') (h : ∀ r, f' (φ r) = φ (f r)) (T : LocLat G ℚ_[l] K O) (g : G)
    (z : TW R T) : TWact f' T g (TWincl φ T z) = TWincl φ T (TWact f T g z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul w y =>
    simp only [TWact, TWincl, TensorProduct.map_tmul, AlgHom.toLinearMap_apply, LinearMap.id_apply, h]
  | add x y hx hy => simp only [map_add, hx, hy]

end Tensor

omit [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [IsUltrametricDist K] [IsUnitBall O K]
  [TameDescentExponentData K l e a] [NeZero a] [NeZero e] [NormedAlgebra ℚ_[l] K] in

theorem galOB_toB (s : GQ l) (x : OA l O) : galOB O s (toB l O x) = toB l O (galOA O s x) := by
  rw [toB, AlgHom.comp_apply, AlgHom.comp_apply, galOB_toOB, galOCr_toOCr]

theorem actB_jB_of_mem_L {ι : Type} [Fintype ι] [DecidableEq ι] {P : PhiMod O K l e a ι}
    {T : LocLat (Gl l) ℚ_[l] K O} {I : Ident t ϖ P T} {jB : (ι → OB l O) ≃ₗ[OB l O] TW (OB l O) T}
    {Δ : Descent P} (hcmp : IsCrisCmp I jB) (hdesc : IsGalDesc (sQ l) I Δ) {g : Gl l}
    {γ : TameGal K l e a} (hc : Covers K t ϖ (sQ l g) γ) {v v' : Vec K a ι} (hv : v ∈ P.L) (hv' : v' ∈ P.L)
    (hvv : v' = Δ.act γ v) (hS : v ∈ P.MMl) (hS' : v' ∈ P.MMl) :
    actB (sQ l) T g (jB (toBcris t ϖ P ⟨v, hS⟩)) = jB (toBcris t ϖ P ⟨v', hS'⟩) := by
  set c : ι → OA l O := fun i => ϖ.iTot t K (coordL P _ ⟨v, hv⟩ i) with hc_def
  set c' : ι → OA l O := fun i => ϖ.iTot t K (coordL P _ ⟨v', hv'⟩ i) with hc'_def
  have hW : toW t ϖ P ⟨v, mem_ME_of_mem_L hv⟩ = inclL t ϖ P c :=
    (toW_toCris_of_mem_L t ϖ P hv (P.ext_mono (A_le_S l e) hv)).1
  have hW' : toW t ϖ P ⟨v', mem_ME_of_mem_L hv'⟩ = inclL t ϖ P c' :=
    (toW_toCris_of_mem_L t ϖ P hv' (P.ext_mono (A_le_S l e) hv')).1
  have hB : toBcris t ϖ P ⟨v, hS⟩ = fun i => toB l O (c i) := funext fun i => by
    rw [toBcris_apply, toB, AlgHom.comp_apply, ← ϖ.iC_of_mem t K, ← ϖ.iB_of_mem t K]
    rfl
  have hB' : toBcris t ϖ P ⟨v', hS'⟩ = fun i => toB l O (c' i) := funext fun i => by
    rw [toBcris_apply, toB, AlgHom.comp_apply, ← ϖ.iC_of_mem t K, ← ϖ.iB_of_mem t K]
    rfl
  have hact : I.act (sQ l g) g (inclL t ϖ P c) = inclL t ϖ P c' := by
    rw [← hW, ← hW']
    exact hdesc g γ hc _ _ hvv
  obtain ⟨α, β, hα, hβ⟩ := P.exists_exponents
  obtain ⟨ε, hε⟩ := (GlobalTheory.T.teichmullerSubOneAinf_properties_compatibleRoots l).1
  obtain ⟨δ, hδ, -⟩ := hε.2
  obtain ⟨-, -, -, hunit, -, -, -⟩ := (GlobalTheory.T.teichmullerSubOneAinf_properties_compatibleRoots l).2 ε δ hε hδ
  obtain ⟨z, hz⟩ := (GlobalTheory.T.breuilKisin_lattice_exponents_ainf_comparison l a e O K t ϖ ι P T I α β hα hβ ε δ hε hδ).2.2.2 _ ⟨c, rfl⟩
  set m : OA l O := 1 ⊗ₜ (muOf ε ^ α) with hm_def
  have key : ∀ (r : OA l O) (d : ι → OA l O), inclL t ϖ P (r • d) = inclO l O r • inclL t ϖ P d := fun r d => by
    rw [inclL_apply, inclL_apply, ← Matrix.mulVec_smul]
    exact congrArg _ (funext fun i => map_mul _ _ _)
  have hsm : ∀ (r : OA l O) (d : ι → OA l O), (fun i => toB l O ((r • d) i)) = toB l O r • fun i => toB l O (d i) :=
    fun r d => funext fun i => by simp only [Pi.smul_apply, smul_eq_mul, map_mul]
  have hA := hcmp (m • c) z (by rw [key]; exact hz)
  rw [hsm, map_smul] at hA
  have hz' : I.j (inclL t ϖ P (galOA O (sQ l g) m • c')) =
      TWincl (inclO l O) T (TWact (galOA O (sQ l g)) T g z) := by
    rw [key, ← galOW_inclO, ← hact, ← I.act_smul, I.j_act, hz,
      TWact_TWincl (inclO l O) (galOA O (sQ l g)) (galOW O (sQ l g)) (galOW_inclO _)]
  have hB2 := hcmp _ _ hz'
  rw [hsm, map_smul, ← TWact_TWincl (toB l O) (galOA O (sQ l g)) (galOB O (sQ l g)) (galOB_toB _), ← hA,
    TWact_smul, galOB_toB] at hB2
  have hmu : IsUnit (toB l O m) := by
    have : toB l O m = (Algebra.TensorProduct.includeRight : Per.Bcris l →ₐ[ℤ_[l]] OB l O)
        (acrisToBcris l (ainfToAcris l (muOf ε))) ^ α := by
      rw [← map_pow, ← map_pow, ← map_pow]
      rfl
    rw [this]
    exact (hunit.map _).pow α
  have hmu' : IsUnit (toB l O (galOA O (sQ l g) m)) := by
    rw [← galOB_toB]
    exact hmu.map _
  rw [hB, hB']
  exact ((hmu'.smul_left_cancel).1 hB2).symm

end GlobalTheory.TameAct

namespace GlobalTheory.TameAct

variable {l : ℕ} [hl : Fact l.Prime] {a e : ℕ} [NeZero a] [NeZero e]
  {O K : Type} [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O]
  [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K]
  [TameDescentExponentData K l e a] {t : Wq l a →ₐ[ℤ_[l]] O} {ϖ : PiSys l e}

theorem toBcris_smul {ι : Type} [Fintype ι] [DecidableEq ι] (P : PhiMod O K l e a ι)
    (F : ZMod a → invL l (S O K e)) (x : Vec K a ι) (hx : x ∈ P.MMl) :
    toBcris t ϖ P ⟨(fun τ => (F τ : K⟦X⟧)) • x, P.smul_tot_mem_ext (fun τ => (F τ).2) hx⟩ =
      ϖ.iB t K F • toBcris t ϖ P ⟨x, hx⟩ := by
  funext i
  rw [Pi.smul_apply, toBcris_apply, toBcris_apply, smul_eq_mul, ← map_mul]
  congr 1
  funext τ
  apply Subtype.ext
  change (P.mxInv τ *ᵥ ((F τ : K⟦X⟧) • x τ)) i = (F τ : K⟦X⟧) * (P.mxInv τ *ᵥ x τ) i
  rw [Matrix.mulVec_smul]
  rfl

theorem actB_jB_toBcris {ι : Type} [Fintype ι] [DecidableEq ι] {P : PhiMod O K l e a ι}
    {T : LocLat (Gl l) ℚ_[l] K O} {I : Ident t ϖ P T} {jB : (ι → OB l O) ≃ₗ[OB l O] TW (OB l O) T}
    {Δ : Descent P} (hcmp : IsCrisCmp I jB) (hdesc : IsGalDesc (sQ l) I Δ) {g : Gl l}
    {γ : TameGal K l e a} (hc : Covers K t ϖ (sQ l g) γ) (σ σ' : P.MMl) (hσ : σ'.1 = Δ.act γ σ.1) :
    actB (sQ l) T g (jB (toBcris t ϖ P σ)) = jB (toBcris t ϖ P σ') := by
  let f : ι → ZMod a → invL l (S O K e) := fun i => coordL P _ σ i
  let f' : ι → ZMod a → invL l (S O K e) := fun i τ =>
    ⟨ringAct γ (fun τ' => (f i τ' : K⟦X⟧)) τ, (rot_S.invL).ringAct_mem γ (fun τ' => (f i τ').2) τ⟩
  let w : ι → Vec K a ι := fun i => P.phi (bas i)
  let w' : ι → Vec K a ι := fun i => Δ.act γ (w i)
  have hw : ∀ i, w i ∈ P.L := fun i => P.phi_mem_L (P.bas_mem_M i)
  have hw' : ∀ i, w' i ∈ P.L := fun i => by
    change Δ.act γ (P.phi (bas i)) ∈ P.L
    rw [Δ.act_phi]
    exact P.phi_mem_L (Δ.act_mem_M γ _ (P.bas_mem_M i))
  have hwS : ∀ i, w i ∈ P.MMl := fun i => P.ext_mono ((A_le_S l e).trans (le_away _ _)) (hw i)
  have hwS' : ∀ i, w' i ∈ P.MMl := fun i => P.ext_mono ((A_le_S l e).trans (le_away _ _)) (hw' i)
  have e1 : σ = ∑ i, (⟨(fun τ => (f i τ : K⟦X⟧)) • w i,
      P.smul_tot_mem_ext (fun τ => (f i τ).2) (hwS i)⟩ : P.MMl) := by
    apply Subtype.ext
    rw [Submodule.coe_sum]
    exact P.eq_sum_phi_bas σ.1
  have e2 : σ' = ∑ i, (⟨(fun τ => (f' i τ : K⟦X⟧)) • w' i,
      P.smul_tot_mem_ext (fun τ => (f' i τ).2) (hwS' i)⟩ : P.MMl) := by
    apply Subtype.ext
    rw [Submodule.coe_sum, hσ]
    conv_lhs => rw [P.eq_sum_phi_bas σ.1]
    rw [map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Δ.act_smul_tot]
    rfl
  rw [e1, e2, map_sum, map_sum, map_sum, map_sum, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hL := actB_jB_of_mem_L hcmp hdesc hc (hw i) (hw' i) rfl (hwS i) (hwS' i)
  rw [toBcris_smul P (f i) (w i) (hwS i), toBcris_smul P (f' i) (w' i) (hwS' i), jB.map_smul, jB.map_smul]
  change TWact (galOB O (sQ l g)) T g (_ • _) = _
  rw [TWact_smul]
  change _ • actB (sQ l) T g _ = _
  rw [hL, galOB_iB_of_covers t ϖ hc (f i) (f' i) (fun τ => rfl)]

end GlobalTheory.TameAct

theorem GlobalTheory.TameAct.main : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (O K : Type) [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] [TameDescentExponentData K l e a] (t : Wq l a →ₐ[ℤ_[l]] O) (ϖ : PiSys l e) (ι : Type) [Fintype ι] [DecidableEq ι] (P : PhiMod O K l e a ι) (T : LocLat (Gl l) ℚ_[l] K O) (I : Ident t ϖ P T) (jB : (ι → OB l O) ≃ₗ[OB l O] TW (OB l O) T) (Δ : Descent P), IsCrisCmp I jB → IsGalDesc (sQ l) I Δ → ∀ (g : Gl l) (γ : TameGal K l e a), Covers K t ϖ (sQ l g) γ → ∀ σ σ' : P.MMl, σ'.1 = Δ.act γ σ.1 → actB (sQ l) T g (jB (toBcris t ϖ P σ)) = jB (toBcris t ϖ P σ') :=
  fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hcmp hdesc _ _ hc σ σ' hσ =>
    GlobalTheory.TameAct.actB_jB_toBcris hcmp hdesc hc σ σ' hσ
