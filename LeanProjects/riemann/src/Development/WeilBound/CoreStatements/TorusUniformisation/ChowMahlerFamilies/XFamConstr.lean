import Mathlib
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.IsLatticeFamily
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.BundleChernComparison
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.LocallyFreeFiniteProjectiveBaseChange
open MvPolynomial GlobalTheory.CompanionTheory.Ar.Num GroundTheory.Heights₂.Heights.NumbersDVR
open ReciprocityTheory.ChartRestriction.G.Geo (ChartBundle chartRing)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg mcIdeal chartMon joinCoord bcCoord pullDeg restrictChart fnField ck rootNum SameGeneric LatLE IsPull IsPullBC)

namespace PositivityTheory.Xgn.A_fam_constr

open ReciprocityTheory.ChartRestriction.G.Geo (exists_pow_mul_mem_chartRing div_mem_chartRing)

variable {o : Type} [CommRing o] {Ω : Type} [Field Ω] [Algebra o Ω]
variable {K : Type} [Fintype K] {ι : K → Type} {x : (Σ k, ι k) → Ω}
variable {V V₁ : Type} [AddCommGroup V] [Module Ω V] [AddCommGroup V₁] [Module Ω V₁]

theorem mono {Γ : (∀ k, ι k) → AddSubgroup V} (h : IsLatFamily o x Γ) {s t : ∀ k, ι k}
    (ht : mseg x t ≠ 0) {v : V} {m m' : ℕ} (hm : m ≤ m') (hv : (mseg x s / mseg x t) ^ m • v ∈ Γ t) :
    (mseg x s / mseg x t) ^ m' • v ∈ Γ t := by
  rw [← Nat.sub_add_cancel hm, pow_add, mul_smul]
  exact h.1 t ht _ (pow_mem (div_mem_chartRing (mseg x) t s) _) _ hv

theorem fam_sub (U : Submodule Ω V) : IsLatFamily o x (fun _ => U.toAddSubgroup) :=
  ⟨fun _ _ a _ _ hv => U.smul_mem a hv, fun _ _ _ _ _ hv => ⟨0, U.smul_mem _ hv⟩⟩

theorem fam_top : IsLatFamily o x (fun _ => (⊤ : AddSubgroup V)) :=
  ⟨fun _ _ _ _ _ _ => trivial, fun _ _ _ _ _ _ => ⟨0, trivial⟩⟩

theorem fam_bot : IsLatFamily o x (fun _ => (⊥ : AddSubgroup V)) := fam_sub ⊥

theorem fam_sup {A B : (∀ k, ι k) → AddSubgroup V} (hA : IsLatFamily o x A) (hB : IsLatFamily o x B) :
    IsLatFamily o x (fun c => A c ⊔ B c) := by
  refine ⟨fun s hs a ha v hv => ?_, fun s t hs ht v hv => ?_⟩
  · obtain ⟨y, hy, z, hz, rfl⟩ := AddSubgroup.mem_sup.1 hv
    rw [smul_add]
    exact AddSubgroup.add_mem_sup (hA.1 s hs a ha y hy) (hB.1 s hs a ha z hz)
  · obtain ⟨y, hy, z, hz, rfl⟩ := AddSubgroup.mem_sup.1 hv
    obtain ⟨m, hm⟩ := hA.2 s t hs ht y hy
    obtain ⟨m', hm'⟩ := hB.2 s t hs ht z hz
    refine ⟨m + m', ?_⟩
    rw [smul_add]
    exact AddSubgroup.add_mem_sup (mono hA ht (Nat.le_add_right _ _) hm)
      (mono hB ht (Nat.le_add_left _ _) hm')

theorem fam_inf {A B : (∀ k, ι k) → AddSubgroup V} (hA : IsLatFamily o x A) (hB : IsLatFamily o x B) :
    IsLatFamily o x (fun c => A c ⊓ B c) := by
  refine ⟨fun s hs a ha v hv => ⟨hA.1 s hs a ha v hv.1, hB.1 s hs a ha v hv.2⟩,
    fun s t hs ht v hv => ?_⟩
  obtain ⟨m, hm⟩ := hA.2 s t hs ht v hv.1
  obtain ⟨m', hm'⟩ := hB.2 s t hs ht v hv.2
  exact ⟨m + m', mono hA ht (Nat.le_add_right _ _) hm, mono hB ht (Nat.le_add_left _ _) hm'⟩

theorem fam_map {A : (∀ k, ι k) → AddSubgroup V} (hA : IsLatFamily o x A) (f : V →+ V₁)
    (hf : ∀ (a : Ω) v, f (a • v) = a • f v) : IsLatFamily o x (fun c => (A c).map f) := by
  refine ⟨fun s hs a ha v hv => ?_, fun s t hs ht v hv => ?_⟩
  · obtain ⟨y, hy, rfl⟩ := hv
    exact ⟨_, hA.1 s hs a ha y hy, hf a y⟩
  · obtain ⟨y, hy, rfl⟩ := hv
    obtain ⟨m, hm⟩ := hA.2 s t hs ht y hy
    exact ⟨m, _, hm, hf _ y⟩

theorem fam_comap {A : (∀ k, ι k) → AddSubgroup V₁} (hA : IsLatFamily o x A) (f : V →+ V₁)
    (hf : ∀ (a : Ω) v, f (a • v) = a • f v) : IsLatFamily o x (fun c => (A c).comap f) := by
  refine ⟨fun s hs a ha v hv => ?_, fun s t hs ht v hv => ?_⟩
  · rw [AddSubgroup.mem_comap, hf]
    exact hA.1 s hs a ha _ hv
  · obtain ⟨m, hm⟩ := hA.2 s t hs ht _ hv
    exact ⟨m, by rw [AddSubgroup.mem_comap, hf]; exact hm⟩

theorem fam_prod {A : (∀ k, ι k) → AddSubgroup V} {B : (∀ k, ι k) → AddSubgroup V₁}
    (hA : IsLatFamily o x A) (hB : IsLatFamily o x B) :
    IsLatFamily o x (fun c => (A c).prod (B c)) := by
  refine ⟨fun s hs a ha v hv => ⟨hA.1 s hs a ha _ hv.1, hB.1 s hs a ha _ hv.2⟩,
    fun s t hs ht v hv => ?_⟩
  obtain ⟨m, hm⟩ := hA.2 s t hs ht _ hv.1
  obtain ⟨m', hm'⟩ := hB.2 s t hs ht _ hv.2
  exact ⟨m + m', mono hA ht (Nat.le_add_right _ _) hm, mono hB ht (Nat.le_add_left _ _) hm'⟩

theorem mem_stdLat (R : Subalgebra o Ω) {J : Type} (v : J → Ω) : v ∈ stdLat R J ↔ ∀ j, v j ∈ R :=
  ⟨fun h j => h j trivial, fun h j _ => h j⟩

theorem fam_std (J : Type) [Fintype J] :
    IsLatFamily o x (fun c => stdLat (chartRing o (mseg x) c) J) := by
  refine ⟨fun s _ a ha v hv => ?_, fun s t hs _ v hv => ?_⟩
  · rw [mem_stdLat] at hv ⊢
    exact fun j => mul_mem ha (hv j)
  · rw [mem_stdLat] at hv
    choose m hm using fun j => exists_pow_mul_mem_chartRing (mseg x) s t hs (hv j)
    refine ⟨∑ q, m q, (mem_stdLat _ _).2 fun q => ?_⟩
    have hle : m q ≤ ∑ q, m q :=
      Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ q)
    rw [Pi.smul_apply, smul_eq_mul, ← Nat.sub_add_cancel hle, pow_add, mul_assoc]
    exact mul_mem (pow_mem (div_mem_chartRing (mseg x) t s) _) (hm q)

theorem mem_dotDual (R : Subalgebra o Ω) {m : ℕ} (L : AddSubgroup (Fin m → Ω)) (w : Fin m → Ω) :
    w ∈ dotDual R L ↔ ∀ v ∈ L, v ⬝ᵥ w ∈ R := by
  simp only [dotDual, AddSubgroup.mem_iInf, AddSubgroup.mem_comap]
  rfl

def FG (R : Subalgebra o Ω) (L : AddSubgroup V) : Prop :=
  ∃ (I : Type) (_ : Fintype I) (g : I → V), (∀ i, g i ∈ L) ∧
    ∀ e ∈ L, ∃ a : I → Ω, (∀ i, a i ∈ R) ∧ ∑ i, a i • g i = e

theorem fg_of_locFree {R : Subalgebra o Ω} {r : ℕ} {L : AddSubgroup V} (h : LocFree R r L) :
    FG R L := by
  let L' : Submodule R V := { L with smul_mem' := fun a e he => h.1 a a.2 e he }
  obtain ⟨k, φ, v, hφ, hv⟩ := LocFreeProj.exists_dualBasis (L := L') (r := r) h
  exact ⟨_, inferInstance, fun i => v i, fun i => (v i).2,
    fun e he => ⟨fun i => φ i e, fun i => hφ i e he, hv e⟩⟩

theorem fg_comap {R : Subalgebra o Ω} {L : AddSubgroup V₁} (h : FG R L) (f : V →ₗ[Ω] V₁)
    (hf : Function.Injective f) (hS : Summand L (LinearMap.range f)) :
    FG R (L.comap f.toAddMonoidHom) := by
  obtain ⟨I, hI, g, hg, hL⟩ := h
  obtain ⟨ρ, h1, h2, h3⟩ := hS
  choose y hy using fun i => h1 (g i)
  refine ⟨I, hI, y, fun i => ?_, fun e he => ?_⟩
  · change f (y i) ∈ L
    rw [hy]
    exact h3 _ (hg i)
  · obtain ⟨a, ha, hs⟩ := hL (f e) he
    refine ⟨a, ha, hf ?_⟩
    rw [← h2 (f e) ⟨e, rfl⟩, ← hs]
    simp only [map_sum, map_smul, hy]

theorem fam_dual {m : ℕ} {A : (∀ k, ι k) → AddSubgroup (Fin m → Ω)} (hA : IsLatFamily o x A)
    (hfg : ∀ c, mseg x c ≠ 0 → FG (chartRing o (mseg x) c) (A c)) :
    IsLatFamily o x (fun c => dotDual (chartRing o (mseg x) c) (A c)) := by
  refine ⟨fun s _ a ha w hw => ?_, fun s t hs ht w hw => ?_⟩
  · rw [mem_dotDual] at hw ⊢
    intro v hv
    rw [dotProduct_smul, smul_eq_mul]
    exact mul_mem ha (hw v hv)
  · rw [mem_dotDual] at hw
    obtain ⟨I, hI, g, hg, hL⟩ := hfg t ht
    have key : ∀ i, ∃ k : ℕ, (mseg x s / mseg x t) ^ k * (g i ⬝ᵥ w) ∈ chartRing o (mseg x) t := by
      intro i
      obtain ⟨k, hk⟩ := hA.2 t s ht hs _ (hg i)
      obtain ⟨k', hk'⟩ := exists_pow_mul_mem_chartRing (mseg x) s t hs (hw _ hk)
      refine ⟨k', ?_⟩
      have hu : (mseg x s / mseg x t) ^ k * (mseg x t / mseg x s) ^ k = 1 := by
        rw [← mul_pow, div_mul_div_comm, mul_comm (mseg x s), div_self (mul_ne_zero ht hs), one_pow]
      rw [smul_dotProduct, smul_eq_mul] at hk'
      have : (mseg x s / mseg x t) ^ k' * (g i ⬝ᵥ w) = (mseg x s / mseg x t) ^ k *
          ((mseg x s / mseg x t) ^ k' * ((mseg x t / mseg x s) ^ k * (g i ⬝ᵥ w))) := by
        linear_combination (-(mseg x s / mseg x t) ^ k' * (g i ⬝ᵥ w)) * hu
      rw [this]
      exact mul_mem (pow_mem (div_mem_chartRing (mseg x) t s) _) hk'
    choose k hk using key
    refine ⟨∑ q, k q, (mem_dotDual _ _ _).2 fun v hv => ?_⟩
    obtain ⟨a, ha, rfl⟩ := hL v hv
    rw [sum_dotProduct]
    refine sum_mem fun q _ => ?_
    have hle : k q ≤ ∑ q, k q :=
      Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ q)
    rw [smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul, ← Nat.sub_add_cancel hle, pow_add,
      mul_assoc]
    exact mul_mem (ha q) (mul_mem (pow_mem (div_mem_chartRing (mseg x) t s) _) (hk q))

theorem linMap_inj {F : Type} [Zero F] [One F] (n : ℕ) (χ : F → Ω) (h0 : χ 0 = 0) (h1 : χ 1 = 1) :
    Function.Injective (linMap n χ) := by
  rw [injective_iff_map_eq_zero]
  intro l hl
  funext j
  have := congrFun hl (Pi.single j 1)
  rw [linMap, Fintype.linearCombination_apply, Finset.sum_apply, Finset.sum_eq_single j] at this
  · simpa [h1] using this
  · intro i _ hi
    simp [Pi.single_eq_of_ne hi, h0]
  · simp

end PositivityTheory.Xgn.A_fam_constr

open PositivityTheory.Xgn.A_fam_constr in
theorem PositivityTheory.Xgn.t_fam_constr : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (Ω : Type) [Field Ω] [Algebra O Ω] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (x : (Σ k, ι k) → Ω), Function.Injective (algebraMap O Ω) → ∀ {F : Type} [Zero F] [One F] [Fintype F] {n : ℕ} {Sg : Type} [Fintype Sg] {r s : Sg → ℕ} (p : ℕ), p.Prime → ∀ (w : O) (χ : Sg → F → O) (φ : Equiv.Perm Sg) (D : (∀ k, ι k) → LieLatticeData Ω F n Sg r s), IsLatticeFamily O x p w χ φ D → IsLatFamily O x (fun c => (D c).l1 (chartRing O (mseg x) c) p) ∧ ∀ τ, IsLatFamily O x (fun c => (D c).af (chartRing O (mseg x) c) p (fun a => algebraMap O Ω (χ τ a))) ∧ (∀ i, IsLatFamily O x (fun c => (D c).xId (fun a => algebraMap O Ω (χ τ a)) i) ∧ IsLatFamily O x (fun c => (D c).stepGraph τ (fun a => algebraMap O Ω (χ τ a)) i)) ∧ (∀ i, IsLatFamily O x (fun c => (D c).kk τ i)) ∧ IsLatFamily O x (fun c => dotDual (chartRing O (mseg x) c) ((D c).lie τ)) ∧ ((∀ c, mseg x c ≠ 0 → (D c).Good₁ (chartRing O (mseg x) c) p (fun τ a => algebraMap O Ω (χ τ a))) → IsLatFamily O x (fun c => (D c).hh (chartRing O (mseg x) c) p (fun a => algebraMap O Ω (χ τ a))) ∧ IsLatFamily O x (fun c => (D c).imH (chartRing O (mseg x) c) p τ (fun a => algebraMap O Ω (χ τ a)))) := by
  classical
  intro O _ _ _ Ω _ _ K _ _ ι _ x _ F _ _ _ n Sg _ r s p _ w χ φ D hD
  have hl1 : IsLatFamily O x (fun c => (D c).l1 (chartRing O (mseg x) c) p) :=
    fam_sup hD.famM (fam_map (fam_std _) _ fun a v => smul_comm _ _ _)
  refine ⟨hl1, fun τ => ?_⟩
  obtain ⟨hlie, -, -, -, -, hDel, hTh⟩ := hD.fam τ
  have haf : IsLatFamily O x
      (fun c => (D c).af (chartRing O (mseg x) c) p (fun a => algebraMap O Ω (χ τ a))) :=
    fam_comap hl1 _ fun a v => (linMap n (fun a => algebraMap O Ω (χ τ a))).map_smul a v
  refine ⟨haf, fun i => ⟨?_, ?_⟩, fun i => ?_, ?_, fun hG => ?_⟩
  · exact fam_comap (fam_sup hD.famM (fam_sub _)) _
      fun a v => (LinearMap.toSpanSingleton Ω _ _).map_smul a v
  · exact fam_comap (fam_sup hTh (fam_prod (fam_sub _) fam_bot)) _
      fun a v => Prod.ext ((LinearMap.toSpanSingleton Ω _ _).map_smul a v.1) rfl
  · exact fam_map (fam_inf hTh (fam_prod (fam_sub _) fam_top)) _ fun a v => rfl
  · exact fam_dual hlie fun c hc => fg_of_locFree ((hD.base c hc).free τ).1
  · have hh : IsLatFamily O x
        (fun c => (D c).hh (chartRing O (mseg x) c) p (fun a => algebraMap O Ω (χ τ a))) := by
      refine fam_dual haf fun c hc => fg_comap (fg_of_locFree (hG c hc).l1) _
        (linMap_inj n _ ?_ ?_) ((hG c hc).lin τ)
      · simp [(hD.char.2.2.2.2 τ).1]
      · simp [(hD.char.2.2.2.2 τ).2]
    exact ⟨hh, fam_map (fam_inf hDel (fam_prod hh fam_top)) _ fun a v => rfl⟩
