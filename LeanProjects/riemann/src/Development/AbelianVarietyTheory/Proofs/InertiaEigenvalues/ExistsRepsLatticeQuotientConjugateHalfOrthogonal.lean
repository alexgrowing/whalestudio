import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HasShape
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsNsmulIntMemLatO

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DownLift
open GlobalTheory.DownLift.GenFinite
open GlobalTheory.DownLift.SplitCoef

noncomputable section

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

namespace GlobalTheory.DownLift.GenQuot

open GlobalTheory.PlaceModel

variable {D : D7} {S T : HSp D}

theorem symplO_nsmul_swap (k : ℕ) (x y : WO S T) : symplO S T (k • x) y = symplO S T x (k • y) := by
  induction k with
  | zero => simp only [zero_smul, symplO_zero_left, symplO_zero_right]
  | succ n ih => rw [succ_nsmul, succ_nsmul, symplO_add_left, symplO_add_right, ih]

theorem reps_orth : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D), IsStdChar D ψ (-1) → ∀ (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)), IsSelfDualC S ΛS → IsSelfDualC T ΛT → ∀ a : AE D, a * a = a → infPart D a = 0 → ∀ k : ℕ, 0 < k → ∃ Y : Finset (WO S T), Y.Nonempty ∧ (∀ y ∈ Y, IsHalf (cA D a) y ∧ k • y ∈ latH S T ΛS ΛT) ∧ (∀ y', IsHalf (cA D a) y' → k • y' ∈ latH S T ΛS ΛT → ∃! y, y ∈ Y ∧ ∃ u ∈ latH S T ΛS ΛT, IsHalf (cA D a) u ∧ y' - y = k • u) ∧ ∀ x, IsHalf a x → k • x ∈ latH S T ΛS ΛT → ((∃ u ∈ latH S T ΛS ΛT, IsHalf a u ∧ x = k • u) → ∀ y ∈ Y, ψ (symplO S T x y) = 1) ∧ ((¬ ∃ u ∈ latH S T ΛS ΛT, IsHalf a u ∧ x = k • u) → ∑ y ∈ Y, ψ (symplO S T x y) = 0) := by
  intro D ψ S T hψ ΛS ΛT hS hT a ha hinf k hk
  classical
  have hdual : ∀ u : WO S T, u.map (infPart D) = 0 →
      (u ∈ latH S T ΛS ΛT ↔ ∀ u' ∈ latH S T ΛS ΛT, ψ (symplO S T u u') = 1) :=
    (GlobalTheory.LatVac.latO_selfDual_approx_sign D ψ S T _ _ hψ hS hT).1
  have hfin : ∀ m : ℕ, 0 < m → ∃ R : Set (WO S T), R.Finite ∧
      ∀ t ∈ latH S T ΛS ΛT, ∃ r ∈ R, ∃ u ∈ latH S T ΛS ΛT, t = r + m • u :=
    GlobalTheory.LatFinMod.latO_finite_mod D S T _ _ hS.1.fg hT.1.fg fun _ => True
  have hsm : ∀ {b : AE D}, b * b = b → ∀ u ∈ latH S T ΛS ΛT, b • u ∈ latH S T ΛS ΛT ⊓ half S T b :=
    fun {b} hb u hu =>
    ⟨GlobalTheory.LatticeStable.smul_mem_latO D S T _ _ _ b
      (GlobalTheory.AdIdem.idempotent_mem_intAE D _ (by rw [← RingHom.map_mul, hb])) u hu,
      (mem_half S T).2 (by rw [smul_smul, hb])⟩
  generalize latH S T ΛS ΛT = Λ at *
  have hc : cA D a * cA D a = cA D a := by rw [← RingHom.map_mul, ha]
  generalize hcdef : cA D a = c at *
  have tf : Function.Injective fun t : WO S T => k • t := fun x y hxy => by
    rw [← inv_smul_nsmul S T hk x, ← inv_smul_nsmul S T hk y]
    exact congrArg _ hxy

  let M : AddSubgroup (WO S T) := half S T c ⊓ Λ.comap (nsmulAddMonoidHom k)
  let N : AddSubgroup (WO S T) := (Λ ⊓ half S T c).map (nsmulAddMonoidHom k)
  have hM : ∀ y, y ∈ M ↔ IsHalf c y ∧ k • y ∈ Λ := fun y => by
    rw [isHalf_iff]; rfl
  have hN : ∀ n, n ∈ N ↔ ∃ u ∈ Λ, IsHalf c u ∧ n = k • u := fun n => by
    constructor
    · rintro ⟨u, hu, rfl⟩
      exact ⟨u, hu.1, (isHalf_iff S T).2 hu.2, rfl⟩
    · rintro ⟨u, hu, hu', rfl⟩
      exact ⟨u, ⟨hu, (isHalf_iff S T).1 hu'⟩, rfl⟩
  let N' : AddSubgroup M := N.addSubgroupOf M
  have hq : ∀ y₁ y₂ : M, ((y₁ : M ⧸ N') = y₂ ↔ (y₂ : WO S T) - y₁ ∈ N) := fun y₁ y₂ => by
    rw [QuotientAddGroup.eq, AddSubgroup.mem_addSubgroupOf]
    simp only [AddSubgroup.coe_add, AddSubgroup.coe_neg]
    rw [neg_add_eq_sub]

  obtain ⟨R2, hR2, hR2'⟩ := hfin (k * k) (Nat.mul_pos hk hk)
  have hP : ((fun t : WO S T => k • t) ⁻¹' ((fun r => c • r) '' R2)).Finite :=
    (hR2.image _).preimage tf.injOn
  have hcover : ∀ y : M, ∃ z : M, (z : WO S T) ∈ (fun t : WO S T => k • t) ⁻¹' ((fun r => c • r) '' R2) ∧
      (z : M ⧸ N') = y := by
    rintro ⟨y, hy⟩
    obtain ⟨hyc, hyk⟩ := (hM y).1 hy
    obtain ⟨r, hr, u, hu, hru⟩ := hR2' _ hyk
    have hcu := hsm hc u hu
    have hky : c • (k • y) = k • y := by
      rw [smul_comm]; exact congrArg (k • ·) ((mem_half S T).1 ((isHalf_iff S T).1 hyc))
    have hz : k • (y - k • (c • u)) = c • r := by
      rw [smul_sub, ← hky, hru, smul_add, mul_smul, smul_comm c k (k • u), smul_comm c k u]
      abel
    have hzM : y - k • (c • u) ∈ M := by
      refine (hM _).2 ⟨(isHalf_iff S T).2 ?_, ?_⟩
      · exact sub_mem ((isHalf_iff S T).1 hyc) (nsmul_mem hcu.2 k)
      · rw [smul_sub]
        exact sub_mem hyk (nsmul_mem (nsmul_mem hcu.1 k) k)
    refine ⟨⟨_, hzM⟩, ⟨r, hr, hz.symm⟩, (hq _ _).2 ?_⟩
    show y - (y - k • (c • u)) ∈ N
    rw [sub_sub_cancel]
    exact ⟨c • u, hcu, rfl⟩
  haveI hfinQ : Finite (M ⧸ N') := by
    let P' : Set M := {z | (z : WO S T) ∈ (fun t : WO S T => k • t) ⁻¹' ((fun r => c • r) '' R2)}
    have hP' : P'.Finite := hP.preimage Subtype.val_injective.injOn
    haveI := hP'.to_subtype
    refine Finite.of_surjective (fun z : P' => ((z : M) : M ⧸ N')) fun q => ?_
    induction q using QuotientAddGroup.induction_on with
    | H y =>
      obtain ⟨z, hz, hzy⟩ := hcover y
      exact ⟨⟨z, hz⟩, hzy⟩
  letI := Fintype.ofFinite (M ⧸ N')
  let rep : M ⧸ N' → WO S T := fun q => ((Quotient.out q : M) : WO S T)
  have hrepM : ∀ q, rep q ∈ M := fun q => (Quotient.out q : M).2
  have hrep : ∀ q, ((⟨rep q, hrepM q⟩ : M) : M ⧸ N') = q := fun q => QuotientAddGroup.out_eq' q
  have hrepinj : Function.Injective rep := fun q₁ q₂ h => by
    rw [← hrep q₁, ← hrep q₂]
    simp only [h]
  refine ⟨Finset.univ.image rep, ⟨rep 0, Finset.mem_image_of_mem _ (Finset.mem_univ _)⟩, ?_, ?_, ?_⟩
  · intro y hy
    obtain ⟨q, -, rfl⟩ := Finset.mem_image.1 hy
    exact (hM _).1 (hrepM q)
  · intro y' hy'c hy'k
    have hy'M : y' ∈ M := (hM y').2 ⟨hy'c, hy'k⟩
    refine ⟨rep (⟨y', hy'M⟩ : M), ⟨Finset.mem_image_of_mem _ (Finset.mem_univ _), (hN _).1 ?_⟩, ?_⟩
    · exact (hq _ _).1 (hrep _)
    · rintro y ⟨hyY, hyN⟩
      obtain ⟨q, -, rfl⟩ := Finset.mem_image.1 hyY
      have := (hq ⟨rep q, hrepM q⟩ ⟨y', hy'M⟩).2 ((hN _).2 hyN)
      rw [hrep] at this
      rw [this]
  intro x hx hkx
  have hxfin : ∀ {u : WO S T}, IsHalf a u → u.map (infPart D) = 0 := fun hu =>
    GlobalTheory.PlaceVec.half_infPart hinf ((isHalf_iff S T).1 hu)
  have hkxh : IsHalf a (k • x) := (isHalf_iff S T).2 (nsmul_mem ((isHalf_iff S T).1 hx) k)
  refine ⟨?_, fun hnot => ?_⟩
  · rintro ⟨u, hu, hua, rfl⟩ y hy
    obtain ⟨q, -, rfl⟩ := Finset.mem_image.1 hy
    rw [symplO_nsmul_swap]
    exact (hdual u (hxfin hua)).1 hu _ ((hM _).1 (hrepM q)).2
  ·
    have hconst : ∀ y₁ y₂ : M, (y₁ : M ⧸ N') = y₂ →
        ψ (symplO S T x (y₂ : WO S T)) = ψ (symplO S T x (y₁ : WO S T)) := fun y₁ y₂ h => by
      obtain ⟨u, hu, -, hu'⟩ := (hN _).1 ((hq _ _).1 h)
      have e : (y₂ : WO S T) = y₁ + k • u := by rw [← hu']; abel
      rw [e, symplO_add_right, AddChar.map_add_eq_mul, ← symplO_nsmul_swap,
        (hdual _ (hxfin hkxh)).1 hkx u hu, mul_one]

    obtain ⟨x', hx'h, hx'⟩ := half_div S T a k hk x ((isHalf_iff S T).1 hx)
    have hx'Λ : x' ∉ Λ := fun h => hnot ⟨x', h, (isHalf_iff S T).2 hx'h, hx'.symm⟩
    have hx'fin := hxfin ((isHalf_iff S T).2 hx'h)
    obtain ⟨l, hl, hψl⟩ : ∃ l ∈ Λ, ψ (symplO S T x' l) ≠ 1 := by
      by_contra hcon
      push_neg at hcon
      exact hx'Λ ((hdual x' hx'fin).2 hcon)
    have hl' := hsm hc l hl
    obtain ⟨y₀, hy₀h, hy₀⟩ := half_div S T c k hk _ hl'.2
    have hy₀M : y₀ ∈ M := (hM _).2 ⟨(isHalf_iff S T).2 hy₀h, hy₀ ▸ hl'.1⟩
    have hψ0 : ψ (symplO S T x y₀) ≠ 1 := by
      rw [← hx', symplO_nsmul_swap, hy₀, ← hcdef, ← symplO_smul, (mem_half S T).1 hx'h]
      exact hψl

    have hsum : ∑ y ∈ Finset.univ.image rep, ψ (symplO S T x y) = ∑ q : M ⧸ N', ψ (symplO S T x (rep q)) :=
      Finset.sum_image fun q₁ _ q₂ _ h => hrepinj h
    rw [hsum]
    have hshift : ∑ q : M ⧸ N', ψ (symplO S T x (rep q)) =
        (∑ q : M ⧸ N', ψ (symplO S T x (rep q))) * ψ (symplO S T x y₀) := by
      rw [Finset.sum_mul]
      refine (Fintype.sum_equiv (Equiv.addRight ((⟨y₀, hy₀M⟩ : M) : M ⧸ N')) _ _ fun q => ?_).symm
      rw [← AddChar.map_add_eq_mul, ← symplO_add_right]
      have := hconst (⟨rep q, hrepM q⟩ + ⟨y₀, hy₀M⟩) ⟨rep (q + ((⟨y₀, hy₀M⟩ : M) : M ⧸ N')), hrepM _⟩
        (by rw [hrep, QuotientAddGroup.mk_add, hrep])
      simpa using this.symm
    have h0 : (∑ q : M ⧸ N', ψ (symplO S T x (rep q))) * (ψ (symplO S T x y₀) - 1) = 0 := by
      rw [mul_sub, mul_one, ← hshift, sub_self]
    exact (mul_eq_zero.1 h0).resolve_right (sub_ne_zero.2 hψ0)

end GlobalTheory.DownLift.GenQuot

end
