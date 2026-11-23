import Mathlib
import Formalism.LocalToGlobal.PairingIndexBounds.OrthogonalChartLevels.FdOfCharts
import Formalism.LocalToGlobal.GroupLattices.PendingLemmas.InvarianceRepresentativesLaw
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.NatCastMemOfPlace
import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.AlternatingFormStandardHermitian
import Formalism.LocalToGlobal.InertKernelTheory.InertCoprimeLemmas.RepComb
import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.ThDistC
import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.PeriodLatticeFinitelyGenerated
import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.SelfDualLatticeNorms.SelfDualComap
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F GlobalTheory.TwU TensorProduct
open Formalism.L2.Th1.H Formalism.L2.KerInert.RepComb

noncomputable section

namespace GlobalTheory.CommonReps

def RepsIn {G : Type} [AddCommGroup G] (X Y : AddSubgroup G) (S : Finset G) : Prop :=
  (∀ x ∈ S, x ∈ Y) ∧ (∀ x ∈ S, ∀ y ∈ S, x - y ∈ X → x = y) ∧ ∀ y ∈ Y, ∃ x ∈ S, y - x ∈ X

theorem isReps_map {G V : Type} [AddCommGroup G] [AddCommGroup V] [Module ℂ V] [DecidableEq V] (f : G →+ V)
    (hf : Function.Injective f) {X Y : AddSubgroup G} {S : Finset G} (h : RepsIn X Y S) :
    IsReps (X.map f) (Y.map f) (S.image f) := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨?_, ?_, ?_⟩
  · intro v hv
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 hv
    exact ⟨x, h1 x hx, rfl⟩
  · intro v hv w hw hvw
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 hv
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.1 hw
    obtain ⟨m, hm, hme⟩ := hvw
    rw [← map_sub] at hme
    rw [h2 x hx y hy (hf hme ▸ hm)]
  · rintro _ ⟨y, hy, rfl⟩
    obtain ⟨x, hx, hyx⟩ := h3 y hy
    exact ⟨f x, Finset.mem_image_of_mem f hx, ⟨y - x, hyx, map_sub f y x⟩⟩

theorem repsIn_preimage {G V : Type} [AddCommGroup G] [AddCommGroup V] [Module ℂ V] (f : G →+ V)
    (hf : Function.Injective f) {X Y : AddSubgroup G} {T : Finset V} (h : IsReps (X.map f) (Y.map f) T) :
    RepsIn X Y (T.preimage f hf.injOn) := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨?_, ?_, ?_⟩
  · intro x hx
    obtain ⟨y, hy, hyx⟩ := h1 (f x) (Finset.mem_preimage.1 hx)
    exact hf hyx ▸ hy
  · intro x hx y hy hxy
    exact hf (h2 _ (Finset.mem_preimage.1 hx) _ (Finset.mem_preimage.1 hy) ⟨x - y, hxy, map_sub f x y⟩)
  · intro y hy
    obtain ⟨v, hv, hyv⟩ := h3 (f y) ⟨y, hy, rfl⟩
    obtain ⟨x, -, rfl⟩ := h1 v hv
    refine ⟨x, Finset.mem_preimage.2 hv, ?_⟩
    obtain ⟨m, hm, hme⟩ := hyv
    rw [← map_sub] at hme
    exact hf hme ▸ hm

theorem repsIn_move {R G : Type} [CommRing R] [AddCommGroup G] [Module R G] [DecidableEq G]
    (X Y X₀ Y₀ : Submodule R G) (g c k : R) (hg : g = 1 + c * k)
    (hY : ∀ y ∈ Y, g • y ∈ Y₀) (hY₀ : ∀ y ∈ Y₀, g • y ∈ Y) (hX : ∀ x ∈ X, g • x ∈ X₀) (hX₀ : ∀ x ∈ X₀, g • x ∈ X)
    (hcY : ∀ y ∈ Y, c • y ∈ X) (hcY₀ : ∀ y ∈ Y₀, c • y ∈ X₀) {S₀ : Finset G}
    (hS : RepsIn X₀.toAddSubgroup Y₀.toAddSubgroup S₀) :
    RepsIn X.toAddSubgroup Y.toAddSubgroup (S₀.image (g • ·)) := by
  obtain ⟨h1, h2, h3⟩ := hS
  have hgg : ∀ z : G, z = g • g • z - (2 * k + c * k * k) • (c • z) := by
    intro z
    rw [smul_smul, smul_smul, ← sub_smul, hg]
    have : (1 + c * k) * (1 + c * k) - (2 * k + c * k * k) * c = 1 := by ring
    rw [this, one_smul]
  refine ⟨?_, ?_, ?_⟩
  · intro v hv
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 hv
    exact hY₀ x (h1 x hx)
  · intro v hv w hw hvw
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 hv
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.1 hw
    have hxy : x - y ∈ Y₀ := Y₀.sub_mem (h1 x hx) (h1 y hy)
    have e1 : g • g • (x - y) ∈ X₀ := by
      rw [smul_sub g x y]; exact hX _ hvw
    have e2 : x - y ∈ X₀ := by
      rw [hgg (x - y)]
      exact X₀.sub_mem e1 (X₀.smul_mem _ (hcY₀ _ hxy))
    rw [h2 x hx y hy e2]
  · intro y hy
    obtain ⟨x, hx, hyx⟩ := h3 (g • y) (hY y hy)
    refine ⟨g • x, Finset.mem_image_of_mem _ hx, ?_⟩
    have e : y - g • x = g • (g • y - x) - (2 * k + c * k * k) • (c • y) := by
      conv_lhs => rw [hgg y]
      rw [smul_sub]; abel
    rw [e]
    exact X.sub_mem (hX₀ _ hyx) (X.smul_mem _ (hcY y hy))

theorem common_reps_of {R G V κ : Type} [CommRing R] [AddCommGroup G] [Module R G] [AddCommGroup V] [Module ℂ V]
    (f : G →+ V) (hf : Function.Injective f) (g c k : R) (hg : g = 1 + c * k)
    (X Y : κ → Submodule R G) (X₀ Y₀ : Submodule R G)
    (hY : ∀ i, ∀ y ∈ Y i, g • y ∈ Y₀) (hY₀ : ∀ i, ∀ y ∈ Y₀, g • y ∈ Y i) (hX : ∀ i, ∀ x ∈ X i, g • x ∈ X₀)
    (hX₀ : ∀ i, ∀ x ∈ X₀, g • x ∈ X i) (hcY : ∀ i, ∀ y ∈ Y i, c • y ∈ X i) (hcY₀ : ∀ y ∈ Y₀, c • y ∈ X₀)
    (hidx : relIdx (X₀.toAddSubgroup.map f) (Y₀.toAddSubgroup.map f) ≠ 0) :
    ∃ S : Finset V, ∀ i, IsReps ((X i).toAddSubgroup.map f) ((Y i).toAddSubgroup.map f) S := by
  classical
  have h0 := repsIn_preimage f hf (Formalism.L2.Ker.repsOf_spec _ _ hidx)
  exact ⟨(((Formalism.L2.Ker.repsOf _ _).preimage f hf.injOn).image (g • ·)).image f, fun i =>
    isReps_map f hf (repsIn_move (X i) (Y i) X₀ Y₀ g c k hg (hY i) (hY₀ i) (hX i) (hX₀ i) (hcY i) hcY₀ h0)⟩

section Tw

variable {E : Type} [Field E] [NumberField E] [StarRing E] {W : Type} [AddCommGroup W] [Module E W] [Module (𝓞 E) W]
  [IsScalarTower (𝓞 E) E W]

theorem smul_mem_twO_of (M M₀ : Submodule (𝓞 E) W) (c : ℕ) (e : HeightOneSpectrum (𝓞 E) → ℤ) (g : 𝓞 E)
    (hg : ∀ x ∈ M, g • x ∈ M₀) {x : W} (hx : x ∈ Formalism.L2.Ker.twist₂ M c e) : g • x ∈ Formalism.L2.Ker.twist₂ M₀ c e := by
  rw [Formalism.L2.Ker.mem_twO] at hx ⊢
  intro Q
  obtain ⟨s, hs, hsx⟩ := hx Q
  refine ⟨s, hs, ?_⟩
  rw [smul_comm _ g, smul_comm s g]
  exact hg _ hsx

theorem natsmul_mem_twO (L : Submodule (𝓞 E) W) (c : ℕ) (e e' : HeightOneSpectrum (𝓞 E) → ℤ) (he : ∀ Q, e' Q ≤ e Q + 1)
    {x : W} (hx : x ∈ Formalism.L2.Ker.twist₂ L c e) : (c : 𝓞 E) • x ∈ Formalism.L2.Ker.twist₂ L c e' := by
  rcases Nat.eq_zero_or_pos c with rfl | hc
  · rw [Nat.cast_zero, zero_smul]; exact Submodule.zero_mem _
  have hcE : (c : E) ≠ 0 := by exact_mod_cast hc.ne'
  rw [Formalism.L2.Ker.mem_twO] at hx ⊢
  intro Q
  obtain ⟨n, hn⟩ : ∃ n : ℕ, (n : ℤ) = e Q + 1 - e' Q := ⟨(e Q + 1 - e' Q).toNat, Int.toNat_of_nonneg (by linarith [he Q])⟩
  have key : ((c : E) ^ e' Q)⁻¹ • ((c : 𝓞 E) • x) = ((c : 𝓞 E) ^ n) • (((c : E) ^ e Q)⁻¹ • x) := by
    rw [← IsScalarTower.algebraMap_smul E ((c : 𝓞 E) ^ n), ← IsScalarTower.algebraMap_smul E (c : 𝓞 E) x, smul_smul, smul_smul]
    congr 1
    simp only [map_pow, map_natCast]
    rw [← zpow_neg, ← zpow_neg, ← zpow_natCast, hn, ← zpow_add_one₀ hcE, ← zpow_add₀ hcE]
    congr 1; ring
  rw [key]
  exact Submodule.smul_mem _ _ (hx Q)

theorem mem_twO_zero (M : Submodule (𝓞 E) W) (c : ℕ) (x : W) : x ∈ Formalism.L2.Ker.twist₂ M c (fun _ => 0) ↔ x ∈ M := by
  rw [Formalism.L2.Ker.mem_twO]
  simp only [zpow_zero, inv_one, one_smul]
  exact ⟨fun h => Formalism.L2.Ker.mem_of_forall_locP M h, fun h Q => Formalism.L2.Ker.le_locP' M Q h⟩

end Tw

end GlobalTheory.CommonReps

namespace GlobalTheory.CommonReps

theorem common_reps_halves : ∀ (E : Type) [Field E] [NumberField E] [StarRing E] (ι κ : Type) [Fintype ι] [Nonempty ι] [Fintype κ] (a b : ℕ) (emb : ι → E →+* ℂ) (δ : ℂ) (AA0 : Submodule (𝓞 E) E) (SS : Finset (HeightOneSpectrum (𝓞 E))) (cl : ℕ) (N₀ : Submodule (𝓞 E) (Formalism.L2.Col.Sp E a)) (N₀' : Submodule (𝓞 E) (Formalism.L2.Col.Sp E b)) (N : κ → Submodule (𝓞 E) (Formalism.L2.Col.Sp E a)) (N' : κ → Submodule (𝓞 E) (Formalism.L2.Col.Sp E b)) (g : 𝓞 E), δ ≠ 0 → (∃ k : 𝓞 E, g = 1 + (cl : 𝓞 E) * k) → (∀ i, (∀ x ∈ perO AA0 (N i) (N' i), g • x ∈ perO AA0 N₀ N₀') ∧ ∀ x ∈ perO AA0 N₀ N₀', g • x ∈ perO AA0 (N i) (N' i)) → relIdx (LamC emb δ AA0 N₀ N₀') (AC emb δ AA0 SS N₀ N₀' cl) ≠ 0 → relIdx (BC emb δ AA0 SS N₀ N₀' cl) (LamC emb δ AA0 N₀ N₀' ⊓ AC emb δ AA0 SS N₀ N₀' cl) ≠ 0 → relIdx (LamC emb δ AA0 N₀ N₀') (BC emb δ AA0 SS N₀ N₀' cl) ≠ 0 → ∃ SX SA SB : Finset (VV ι a b), ∀ i, IsReps (LamC emb δ AA0 (N i) (N' i)) (AC emb δ AA0 SS (N i) (N' i) cl) SX ∧ IsReps (BC emb δ AA0 SS (N i) (N' i) cl) (LamC emb δ AA0 (N i) (N' i) ⊓ AC emb δ AA0 SS (N i) (N' i) cl) SA ∧ IsReps (LamC emb δ AA0 (N i) (N' i)) (BC emb δ AA0 SS (N i) (N' i) cl) SB := by
  intro E _ _ _ ι κ _ _ _ a b emb δ AA0 SS cl N₀ N₀' N N' g hδ hk hmv h1 h2 h3
  obtain ⟨k, hk⟩ := hk
  set f : Formalism.L2.Col.HomE E a b →+ VV ι a b := embH emb δ with hfdef
  have hf : Function.Injective f := embH_inj emb hδ
  have hinf : ∀ M A : Submodule (𝓞 E) (Formalism.L2.Col.HomE E a b),
      M.toAddSubgroup.map f ⊓ A.toAddSubgroup.map f = (M ⊓ A).toAddSubgroup.map f := fun M A =>
    (AddSubgroup.map_inf_eq M.toAddSubgroup A.toAddSubgroup f hf).symm
  have hexpS : ∀ Q, expS SS Q ≤ 1 ∧ -1 ≤ expS SS Q := fun Q => by
    rcases Formalism.L2.Ker.expS_cases SS Q with h | h | h <;> rw [h] <;> norm_num

  have hcA : ∀ M : Submodule (𝓞 E) (Formalism.L2.Col.HomE E a b), ∀ y ∈ halfAO SS M cl, (cl : 𝓞 E) • y ∈ M := fun M y hy =>
    (mem_twO_zero M cl _).1 (natsmul_mem_twO M cl _ _ (fun Q => by linarith [(hexpS Q).1]) hy)
  have hcB : ∀ M : Submodule (𝓞 E) (Formalism.L2.Col.HomE E a b), ∀ y ∈ halfBO SS M cl, (cl : 𝓞 E) • y ∈ M := fun M y hy =>
    (mem_twO_zero M cl _).1 (natsmul_mem_twO M cl _ _ (fun Q => by linarith [(hexpS Q).2]) hy)
  have hcM : ∀ M : Submodule (𝓞 E) (Formalism.L2.Col.HomE E a b), ∀ y ∈ M, (cl : 𝓞 E) • y ∈ halfBO SS M cl := fun M y hy =>
    natsmul_mem_twO M cl (fun _ => 0) _ (fun Q => by linarith [(hexpS Q).1]) ((mem_twO_zero M cl y).2 hy)
  have hA : ∀ M M' : Submodule (𝓞 E) (Formalism.L2.Col.HomE E a b), (∀ x ∈ M, g • x ∈ M') → ∀ y ∈ halfAO SS M cl, g • y ∈ halfAO SS M' cl :=
    fun M M' h y hy => smul_mem_twO_of M M' cl _ g h hy
  have hB : ∀ M M' : Submodule (𝓞 E) (Formalism.L2.Col.HomE E a b), (∀ x ∈ M, g • x ∈ M') → ∀ y ∈ halfBO SS M cl, g • y ∈ halfBO SS M' cl :=
    fun M M' h y hy => smul_mem_twO_of M M' cl _ g h hy
  obtain ⟨SX, hSX⟩ := common_reps_of f hf g (cl : 𝓞 E) k hk (fun i => perO AA0 (N i) (N' i))
    (fun i => halfAO SS (perO AA0 (N i) (N' i)) cl) (perO AA0 N₀ N₀') (halfAO SS (perO AA0 N₀ N₀') cl)
    (fun i => hA _ _ (hmv i).1) (fun i => hA _ _ (hmv i).2) (fun i => (hmv i).1) (fun i => (hmv i).2)
    (fun i => hcA _) (hcA _) h1
  have h2' := h2
  simp only [LamC, AC, BC, laV] at h2'
  rw [hinf] at h2'
  obtain ⟨SA, hSA⟩ := common_reps_of f hf g (cl : 𝓞 E) k hk (fun i => halfBO SS (perO AA0 (N i) (N' i)) cl)
    (fun i => perO AA0 (N i) (N' i) ⊓ halfAO SS (perO AA0 (N i) (N' i)) cl) (halfBO SS (perO AA0 N₀ N₀') cl)
    (perO AA0 N₀ N₀' ⊓ halfAO SS (perO AA0 N₀ N₀') cl)
    (fun i y hy => ⟨(hmv i).1 _ hy.1, hA _ _ (hmv i).1 _ hy.2⟩) (fun i y hy => ⟨(hmv i).2 _ hy.1, hA _ _ (hmv i).2 _ hy.2⟩)
    (fun i => hB _ _ (hmv i).1) (fun i => hB _ _ (hmv i).2)
    (fun i y hy => hcM _ y hy.1) (fun y hy => hcM _ y hy.1) h2'
  obtain ⟨SB, hSB⟩ := common_reps_of f hf g (cl : 𝓞 E) k hk (fun i => perO AA0 (N i) (N' i))
    (fun i => halfBO SS (perO AA0 (N i) (N' i)) cl) (perO AA0 N₀ N₀') (halfBO SS (perO AA0 N₀ N₀') cl)
    (fun i => hB _ _ (hmv i).1) (fun i => hB _ _ (hmv i).2) (fun i => (hmv i).1) (fun i => (hmv i).2)
    (fun i => hcB _) (hcB _) h3
  refine ⟨SX, SA, SB, fun i => ⟨hSX i, ?_, hSB i⟩⟩
  have e : LamC emb δ AA0 (N i) (N' i) ⊓ AC emb δ AA0 SS (N i) (N' i) cl =
      (perO AA0 (N i) (N' i) ⊓ halfAO SS (perO AA0 (N i) (N' i)) cl).toAddSubgroup.map f := hinf _ _
  rw [e]
  exact hSA i

end GlobalTheory.CommonReps
