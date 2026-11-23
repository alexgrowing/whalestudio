import Mathlib
import Development.WeilBound.HeckeVectors.HeckeDoubleCosets.DoubleCosetLemmas.LocEval
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IntegralGLCommensuratedDoubleCosetCardInvSymm
import Development.WeilBound.HeckeVectors.HeckeDoubleCosets.DoubleCosetLemmas.DosetIndMemHecke
import Development.WeilBound.HeckeVectors.HeckeDoubleCosets.DoubleCosetLemmas.DosetIndMemMtSub
import Development.WeilBound.HeckeVectors.HeckeDoubleCosets.DoubleCosetLemmas.NeZeroOfIsUnifV
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.SphericalFunctionInvarianceProperties
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.GeneralLinearUnimodularHaar
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.SphericalFunctionTranslateProportional
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.BlockParabolicModulusIntegral
import Development.WeilBound.HeckeVectors.HeckeDoubleCosets.DoubleCosetLemmas.VolumeRankStratum
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.ParabolicTestFunctionEquivariant
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnramifiedZetaSumGLCosets
import Development.AutomorphicSpectrum.Proofs.TwistedProofs.LinActOneOneApply
import Development.AutomorphicSpectrum.Proofs.TwistedProofs.ACo
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PairwiseDisjointCell
import Development.AutomorphicSpectrum.Proofs.TwistedProofs.GaussBinomialTwistedSumIdentity
import Development.AutomorphicSpectrum.Proofs.TwistedProofs.HeckeVecInverseTjSphericalVectorEq
import Formalism.SatakeDualWeyl.KpqSubgroupCompact
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.CartanExponentsNonnegMinusculeTopProduct
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.CardInversePrimeRepsIntegralRightMulHecke

noncomputable section

open NumberField IsDedekindDomain Matrix
open Formalism.UG (Tj Ov qV IsUnifV Hecke IsBiInv conv dosetInd IsCommensurated GLint hAct AMF)
open GlobalTheory.LFun (KGL heckeVec IsSatVecGL satEig seg)
open GlobalTheory.PRep (fixed rightReg)

namespace GlobalTheory.CompanionTheory.Ipf.Val.SphM

section Abs

variable {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V] {K : Subgroup G}

def orb (ρ : Representation ℂ G V) : V →ₗ[ℂ] (G → V) where
  toFun x g := ρ g x
  map_add' x y := by funext g; simp
  map_smul' c x := by funext g; simp

theorem orb_heckeVec (ρ : Representation ℂ G V) (hK : IsCommensurated K) {h : G → ℂ} (hh : h ∈ Hecke ℂ K) (x : V) :
    orb ρ (heckeVec ρ K h x) = hAct K h (orb ρ x) := by
  rw [GlobalTheory.LFun.map_heckeVec hK hh (ρ' := rightReg ℂ G V) (orb ρ) ?_ x, GlobalTheory.LFun.heckeVec_rightReg hK hh]
  intro g y
  funext a
  simp [orb, rightReg]

theorem orb_injective (ρ : Representation ℂ G V) : Function.Injective (orb ρ) := fun a b e => by
  simpa [orb] using congrFun e 1

theorem orb_mem {ρ : Representation ℂ G V} {x : V} (hx : x ∈ fixed ρ K) :
    orb ρ x ∈ AMF ℂ (⊥ : Subgroup G) K (1 : Representation ℂ (⊥ : Subgroup G) V) := by
  rintro ⟨γ, hγ⟩ g ⟨κ, hκ⟩
  have : γ = 1 := hγ
  subst this
  simp [orb, GlobalTheory.LGrp.mem_fixed.1 hx κ hκ]

theorem heckeVec_conv (hK : IsCommensurated K) {f₁ f₂ : G → ℂ} (h₁ : f₁ ∈ Hecke ℂ K) (h₂ : f₂ ∈ Hecke ℂ K)
    (ρ : Representation ℂ G V) {x : V} (hx : x ∈ fixed ρ K) :
    heckeVec ρ K (conv K f₁ f₂) x = heckeVec ρ K f₁ (heckeVec ρ K f₂ x) := by
  apply orb_injective ρ
  rw [orb_heckeVec ρ hK (Formalism.UG.Final.HeckeConvMem G K ℂ hK f₁ h₁ f₂ h₂),
    Formalism.UG.Final.HeckeActMul G ⊥ K ℂ V 1 hK f₁ h₁ f₂ h₂ _ (orb_mem hx), orb_heckeVec ρ hK h₁, orb_heckeVec ρ hK h₂]

theorem heckeVec_add (hK : IsCommensurated K) {f₁ f₂ : G → ℂ} (h₁ : f₁ ∈ Hecke ℂ K) (h₂ : f₂ ∈ Hecke ℂ K)
    (ρ : Representation ℂ G V) (x : V) :
    heckeVec ρ K (f₁ + f₂) x = heckeVec ρ K f₁ x + heckeVec ρ K f₂ x := by
  unfold heckeVec
  rw [← finsum_add_distrib (GlobalTheory.LFun.finite_heckeVec hK h₁ ρ x) (GlobalTheory.LFun.finite_heckeVec hK h₂ ρ x)]
  exact finsum_congr fun c => by simp [add_smul]

theorem heckeVec_smul (z : ℂ) (f : G → ℂ) (ρ : Representation ℂ G V) (x : V) :
    heckeVec ρ K (z • f) x = z • heckeVec ρ K f x := by
  unfold heckeVec
  rw [smul_finsum]
  exact finsum_congr fun c => by simp [mul_smul]

theorem heckeVec_smul_vec (z : ℂ) (f : G → ℂ) (ρ : Representation ℂ G V) (x : V) :
    heckeVec ρ K f (z • x) = z • heckeVec ρ K f x := by
  unfold heckeVec
  rw [smul_finsum]
  exact finsum_congr fun c => by rw [map_smul, smul_comm]

theorem heckeVec_zero (ρ : Representation ℂ G V) (x : V) : heckeVec ρ K (0 : G → ℂ) x = 0 := by
  simp [heckeVec]

theorem heckeVec_sum (hK : IsCommensurated K) {ι : Type} (s : Finset ι) (f : ι → G → ℂ) (hf : ∀ i ∈ s, f i ∈ Hecke ℂ K)
    (ρ : Representation ℂ G V) (x : V) :
    heckeVec ρ K (∑ i ∈ s, f i) x = ∑ i ∈ s, heckeVec ρ K (f i) x := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [heckeVec_zero]
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha,
      heckeVec_add hK (hf a (Finset.mem_insert_self _ _)) (Submodule.sum_mem _ fun i hi => hf i (Finset.mem_insert_of_mem hi)),
      ih fun i hi => hf i (Finset.mem_insert_of_mem hi)]

def finv (f : G → ℂ) : G → ℂ := fun g => f g⁻¹

@[simp] theorem finv_finv (f : G → ℂ) : finv (finv f) = f := by
  funext g; simp [finv]

theorem finv_add (f₁ f₂ : G → ℂ) : finv (f₁ + f₂) = finv f₁ + finv f₂ := rfl
theorem finv_smul (z : ℂ) (f : G → ℂ) : finv (z • f) = z • finv f := rfl
theorem finv_zero : finv (0 : G → ℂ) = 0 := rfl

theorem finv_mem {f : G → ℂ} (hf : f ∈ Hecke ℂ K) : finv f ∈ Hecke ℂ K := by
  classical
  obtain ⟨h1, S, hS⟩ := hf
  refine ⟨fun a b g => ?_, S.image (·⁻¹), fun g hg => ?_⟩
  · have := h1 b⁻¹ a⁻¹ g⁻¹
    simp only [finv]
    rw [← this]
    congr 1
    simp [mul_assoc]
  · obtain ⟨s, hs, a, b, e⟩ := hS g⁻¹ hg
    refine ⟨s⁻¹, Finset.mem_image_of_mem _ hs, b⁻¹, a⁻¹, ?_⟩
    have : g = (g⁻¹)⁻¹ := by simp
    rw [this, e]
    simp [mul_assoc]

end Abs

section Loc

open GlobalTheory.Hk3.MinuscTopLocal (dU)

variable {K : Type} [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))

theorem kComm (n : ℕ) : IsCommensurated (KGL v n) := Formalism.UG.Final.GLintComm K v n

abbrev repS (n c : ℕ) : Representation ℂ (GL (Fin c) (Cv v)) (Matrix (Fin n) (Fin c) (Cv v) → ℂ) :=
  (omega v n c).comp (MonoidHom.inl _ _)

abbrev repT (n c : ℕ) : Representation ℂ (GL (Fin n) (Cv v)) (Matrix (Fin n) (Fin c) (Cv v) → ℂ) :=
  (omega v n c).comp (MonoidHom.inr _ _)

theorem heckeVec_add_vec {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V] {H : Subgroup G} (hK : IsCommensurated H)
    {f : G → ℂ} (hf : f ∈ Hecke ℂ H) (ρ : Representation ℂ G V) (x y : V) :
    heckeVec ρ H f (x + y) = heckeVec ρ H f x + heckeVec ρ H f y := by
  unfold heckeVec
  rw [← finsum_add_distrib (GlobalTheory.LFun.finite_heckeVec hK hf ρ x) (GlobalTheory.LFun.finite_heckeVec hK hf ρ y)]
  exact finsum_congr fun c => by simp

def hop {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V] {H : Subgroup G} (hK : IsCommensurated H)
    {f : G → ℂ} (hf : f ∈ Hecke ℂ H) (ρ : Representation ℂ G V) : V →ₗ[ℂ] V where
  toFun := heckeVec ρ H f
  map_add' := heckeVec_add_vec hK hf ρ
  map_smul' z x := heckeVec_smul_vec z f ρ x

def Eig {n : ℕ} (B : Multiset ℂˣ) (f : GL (Fin n) (Cv v) → ℂ) (μ : ℂ) : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ (GL (Fin n) (Cv v)) V) (x : V),
    IsSatVecGL v ρ x B → heckeVec ρ (KGL v n) f x = μ • x

variable {v}

theorem Eig.add {n : ℕ} {B : Multiset ℂˣ} {f₁ f₂ : GL (Fin n) (Cv v) → ℂ} {μ₁ μ₂ : ℂ}
    (h₁ : Eig v B f₁ μ₁) (h₂ : Eig v B f₂ μ₂) (m₁ : f₁ ∈ Hecke ℂ (KGL v n)) (m₂ : f₂ ∈ Hecke ℂ (KGL v n)) :
    Eig v B (f₁ + f₂) (μ₁ + μ₂) := fun V _ _ ρ x hx => by
  rw [heckeVec_add (kComm v n) m₁ m₂, h₁ V ρ x hx, h₂ V ρ x hx, add_smul]

theorem Eig.smul {n : ℕ} {B : Multiset ℂˣ} {f : GL (Fin n) (Cv v) → ℂ} {μ : ℂ} (z : ℂ)
    (h : Eig v B f μ) : Eig v B (z • f) (z * μ) := fun V _ _ ρ x hx => by
  rw [heckeVec_smul, h V ρ x hx, mul_smul]

theorem eig_zero {n : ℕ} (B : Multiset ℂˣ) : Eig v B (0 : GL (Fin n) (Cv v) → ℂ) 0 := fun V _ _ ρ x _ => by
  rw [heckeVec_zero, zero_smul]

theorem Eig.conv {n : ℕ} {B : Multiset ℂˣ} {f₁ f₂ : GL (Fin n) (Cv v) → ℂ} {μ₁ μ₂ : ℂ}
    (h₁ : Eig v B f₁ μ₁) (h₂ : Eig v B f₂ μ₂) (m₁ : f₁ ∈ Hecke ℂ (KGL v n)) (m₂ : f₂ ∈ Hecke ℂ (KGL v n)) :
    Eig v B (Formalism.UG.conv (KGL v n) f₁ f₂) (μ₁ * μ₂) := fun V _ _ ρ x hx => by
  rw [heckeVec_conv (kComm v n) m₁ m₂ ρ hx.2.1, h₂ V ρ x hx, heckeVec_smul_vec, h₁ V ρ x hx, smul_smul, mul_comm]

theorem Eig.sum {n : ℕ} {B : Multiset ℂˣ} {ι : Type} (s : Finset ι) (f : ι → GL (Fin n) (Cv v) → ℂ) (μ : ι → ℂ)
    (h : ∀ i ∈ s, Eig v B (f i) (μ i)) (m : ∀ i ∈ s, f i ∈ Hecke ℂ (KGL v n)) :
    Eig v B (∑ i ∈ s, f i) (∑ i ∈ s, μ i) := fun V _ _ ρ x hx => by
  rw [heckeVec_sum (kComm v n) s f m, Finset.sum_smul]
  exact Finset.sum_congr rfl fun i hi => h i hi V ρ x hx

variable (v)

def subT (c t : ℕ) : Submodule ℂ (GL (Fin (c + t)) (Cv v) → ℂ) where
  carrier := {f' | f' ∈ Hecke ℂ (KGL v (c + t)) ∧ ∃ f ∈ Hecke ℂ (KGL v c),
    heckeVec (repT v (c + t) c) (KGL v (c + t)) f' (phi0 v (c + t) c) =
      heckeVec (repS v (c + t) c) (KGL v c) f (phi0 v (c + t) c) ∧
    ∀ B : Multiset ℂˣ, B.card = c → ∃ μ, Eig v B (finv f) μ ∧ Eig v (B + seg v 1 t) f' μ}
  zero_mem' := ⟨Submodule.zero_mem _, 0, Submodule.zero_mem _, by rw [heckeVec_zero, heckeVec_zero],
    fun B _ => ⟨0, by rw [finv_zero]; exact eig_zero B, eig_zero _⟩⟩
  add_mem' := by
    rintro a b ⟨ha, f₁, hf₁, e₁, E₁⟩ ⟨hb, f₂, hf₂, e₂, E₂⟩
    refine ⟨Submodule.add_mem _ ha hb, f₁ + f₂, Submodule.add_mem _ hf₁ hf₂, ?_, fun B hB => ?_⟩
    · rw [heckeVec_add (kComm v _) ha hb, heckeVec_add (kComm v _) hf₁ hf₂, e₁, e₂]
    · obtain ⟨μ₁, p₁, q₁⟩ := E₁ B hB
      obtain ⟨μ₂, p₂, q₂⟩ := E₂ B hB
      exact ⟨μ₁ + μ₂, by rw [finv_add]; exact p₁.add p₂ (finv_mem hf₁) (finv_mem hf₂), q₁.add q₂ ha hb⟩
  smul_mem' := by
    rintro z a ⟨ha, f₁, hf₁, e₁, E₁⟩
    refine ⟨Submodule.smul_mem _ z ha, z • f₁, Submodule.smul_mem _ z hf₁, ?_, fun B hB => ?_⟩
    · rw [heckeVec_smul, heckeVec_smul, e₁]
    · obtain ⟨μ₁, p₁, q₁⟩ := E₁ B hB
      exact ⟨z * μ₁, by rw [finv_smul]; exact p₁.smul z, q₁.smul z⟩

def subS (c : ℕ) : Submodule ℂ (GL (Fin c) (Cv v) → ℂ) where
  carrier := {f | f ∈ Hecke ℂ (KGL v c) ∧ ∀ B : Multiset ℂˣ, B.card = c → ∃ μ, Eig v B f μ}
  zero_mem' := ⟨Submodule.zero_mem _, fun B _ => ⟨0, eig_zero B⟩⟩
  add_mem' := by
    rintro a b ⟨ha, E₁⟩ ⟨hb, E₂⟩
    refine ⟨Submodule.add_mem _ ha hb, fun B hB => ?_⟩
    obtain ⟨μ₁, p₁⟩ := E₁ B hB
    obtain ⟨μ₂, p₂⟩ := E₂ B hB
    exact ⟨μ₁ + μ₂, p₁.add p₂ ha hb⟩
  smul_mem' := by
    rintro z a ⟨ha, E₁⟩
    refine ⟨Submodule.smul_mem _ z ha, fun B hB => ?_⟩
    obtain ⟨μ₁, p₁⟩ := E₁ B hB
    exact ⟨z * μ₁, p₁.smul z⟩

theorem heckeVec_central {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V] {H : Subgroup G}
    (ρ : Representation ℂ G V) {x : V} (hx : x ∈ fixed ρ H) {z : G} (hz : ∀ g, z * g = g * z) :
    heckeVec ρ H (dosetInd ℂ H z) x = ρ z x := by
  classical
  have := GlobalTheory.LFun.heckeVec_dosetInd (ρ := ρ) (K := H) hx (a := z) (R := {z})
    (fun γ hγ => by
      rw [Finset.mem_singleton.1 hγ]
      exact DoubleCoset.mem_doubleCoset.2 ⟨1, H.one_mem, 1, H.one_mem, by simp⟩)
    (fun g hg => by
      obtain ⟨a, ha, b, hb, rfl⟩ := DoubleCoset.mem_doubleCoset.1 hg
      refine ⟨z, ⟨Finset.mem_singleton_self _, ?_⟩, fun y hy => Finset.mem_singleton.1 hy.1⟩
      have e : z⁻¹ * (a * z * b) = a * b := by
        rw [← hz a]; group
      rw [e]
      exact H.mul_mem ha hb)
  simpa using this

theorem diagJ_self (n : ℕ) (ϖ : Cv v) : Formalism.UG.diagJ n ϖ n = ϖ • (1 : Matrix (Fin n) (Fin n) (Cv v)) := by
  ext i j
  by_cases h : i = j
  · subst h
    simp [Formalism.UG.diagJ]
  · simp [Formalism.UG.diagJ, h]

def sc (n : ℕ) {ϖ : Cv v} (h0 : ϖ ≠ 0) : GL (Fin n) (Cv v) where
  val := ϖ • 1
  inv := ϖ⁻¹ • 1
  val_inv := by simp [smul_smul, h0]
  inv_val := by simp [smul_smul, h0]

theorem sc_central (n : ℕ) {ϖ : Cv v} (h0 : ϖ ≠ 0) (g : GL (Fin n) (Cv v)) : sc v n h0 * g = g * sc v n h0 :=
  Units.ext (by simp [sc])

theorem Tj_self (n : ℕ) {ϖ : Cv v} (h0 : ϖ ≠ 0) : Tj ℂ n (Ov K v) ϖ n = dosetInd ℂ (KGL v n) (sc v n h0) :=
  Formalism.UG.Final.TjEq (Cv v) (Ov K v) ϖ ℂ n n (sc v n h0) (by rw [diagJ_self]; rfl)

end Loc

end GlobalTheory.CompanionTheory.Ipf.Val.SphM

end
