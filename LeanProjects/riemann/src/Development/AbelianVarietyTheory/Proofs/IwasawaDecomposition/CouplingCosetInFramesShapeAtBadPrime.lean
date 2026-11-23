import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LiftsInvOne
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IntAtNatCast

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.AdT Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.Col2.AdT.CosShape

section Gen

variable {E : Type} [Field E] [NumberField E] {n : ℕ}

theorem pow_smul_mem (S : Submodule (𝓞 E) (Sp E n)) (r : 𝓞 E) (k : ℕ) {x : Sp E n} (hx : x ∈ S) :
    ((r : E) ^ k) • x ∈ S := by

  have h : ((r : E) ^ k) • x = (r ^ k) • x := by
    rw [← algebraMap_smul E (r ^ k) x]
    simp
  rw [h]
  exact S.smul_mem _ hx

theorem core (S₀ L : Submodule (𝓞 E) (Sp E n)) (F : Sp E n ≃ₗ[E] Sp E n) (hF : ∀ w ∈ L, F.symm w ∈ S₀)
    (c : E) (hc : c ≠ 0) (hpow : ∀ (S : Submodule (𝓞 E) (Sp E n)) (k : ℕ) (x : Sp E n), x ∈ S → c ^ k • x ∈ S)
    (Y : Set (Sp E n)) (y₀ : Sp E n) (e e' : ℕ) (hY0 : y₀ ∈ Y) (hY : ∀ y ∈ Y, (c ^ e)⁻¹ • (y - y₀) ∈ L)
    (hy₀ : c ^ e' • y₀ ∈ L) (C : Set (Sp E n)) (hC : ∀ z, z ∈ C ↔ ∃ y ∈ Y, (c ^ e)⁻¹ • (z - F.symm y) ∈ S₀) :
    C.Nonempty ∧ (∀ y ∈ Y, F.symm y ∈ C) ∧ ∀ z ∈ C, (∀ z', z' ∈ C ↔ (c ^ e)⁻¹ • (z' - z) ∈ S₀) ∧
      ∀ (g g' : Sp E n ≃ₗ[E] Sp E n) (D : ℕ), (∀ x, g' x ∈ S₀ ↔ x ∈ S₀) →
        (∀ x ∈ S₀, (c ^ D)⁻¹ • (g x - g' x) ∈ S₀) → e + e' ≤ D →
        (c ^ e)⁻¹ • (g z - z) ∈ S₀ → ∀ z', g' z' ∈ C ↔ z' ∈ C := by

  have hYY : ∀ y ∈ Y, ∀ y' ∈ Y, (c ^ e)⁻¹ • (F.symm y - F.symm y') ∈ S₀ := by
    intro y hy y' hy'
    have h1 := hF _ (hY y hy)
    have h2 := hF _ (hY y' hy')
    have h3 : (c ^ e)⁻¹ • (F.symm y - F.symm y') =
        F.symm ((c ^ e)⁻¹ • (y - y₀)) - F.symm ((c ^ e)⁻¹ • (y' - y₀)) := by
      simp only [LinearEquiv.map_smul, map_sub]
      rw [← smul_sub]
      congr 1
      abel
    rw [h3]
    exact S₀.sub_mem h1 h2
  have hself : ∀ y ∈ Y, F.symm y ∈ C := by
    intro y hy
    exact (hC _).2 ⟨y, hy, by simp⟩

  have hmem : ∀ z ∈ C, ∀ z', z' ∈ C ↔ (c ^ e)⁻¹ • (z' - z) ∈ S₀ := by
    intro z hz z'
    obtain ⟨y₁, hy₁, hz1⟩ := (hC z).1 hz
    constructor
    · intro hz'
      obtain ⟨y₂, hy₂, hz2⟩ := (hC z').1 hz'
      have key := S₀.add_mem (S₀.sub_mem hz2 hz1) (hYY y₂ hy₂ y₁ hy₁)
      convert key using 1
      rw [← smul_sub, ← smul_add]
      congr 1
      abel
    · intro h
      refine (hC z').2 ⟨y₁, hy₁, ?_⟩
      have key := S₀.add_mem h hz1
      convert key using 1
      rw [← smul_add]
      congr 1
      abel
  refine ⟨⟨F.symm y₀, hself y₀ hY0⟩, hself, fun z hz => ⟨hmem z hz, ?_⟩⟩
  intro g g' D hg' hD hle hgz z'
  obtain ⟨y₁, hy₁, hz1⟩ := (hC z).1 hz
  have hce : c ^ e ≠ 0 := pow_ne_zero _ hc

  have hx₀ : c ^ e' • z ∈ S₀ := by
    have a1 : c ^ e' • (c ^ e • ((c ^ e)⁻¹ • (z - F.symm y₁))) ∈ S₀ := hpow _ _ _ (hpow _ _ _ hz1)
    have a2 : c ^ e' • (c ^ e • ((c ^ e)⁻¹ • (F.symm y₁ - F.symm y₀))) ∈ S₀ :=
      hpow _ _ _ (hpow _ _ _ (hYY y₁ hy₁ y₀ hY0))
    have a3 : F.symm (c ^ e' • y₀) ∈ S₀ := hF _ hy₀
    rw [smul_inv_smul₀ hce] at a1 a2
    rw [LinearEquiv.map_smul] at a3
    have a4 := S₀.add_mem (S₀.add_mem a1 a2) a3
    convert a4 using 1
    rw [← smul_add, ← smul_add]
    congr 1
    abel

  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hle
  have hdiff : (c ^ e)⁻¹ • (g z - g' z) ∈ S₀ := by
    have b1 := hpow S₀ k _ (hD _ hx₀)
    convert b1 using 1
    rw [LinearEquiv.map_smul, LinearEquiv.map_smul, ← smul_sub, smul_smul, smul_smul]
    congr 1
    rw [pow_add, pow_add]
    field_simp
  have ht : (c ^ e)⁻¹ • (g' z - z) ∈ S₀ := by
    have b2 := S₀.sub_mem hgz hdiff
    convert b2 using 1
    rw [← smul_sub]
    congr 1
    abel
  rw [hmem z hz (g' z'), hmem z hz z']
  have hsplit : (c ^ e)⁻¹ • (g' z' - z) = g' ((c ^ e)⁻¹ • (z' - z)) + (c ^ e)⁻¹ • (g' z - z) := by
    rw [LinearEquiv.map_smul, ← smul_add, map_sub]
    congr 1
    abel
  rw [hsplit, add_mem_cancel_right ht]
  exact hg' _

end Gen

end GlobalTheory.Mem.Col2.AdT.CosShape

namespace GlobalTheory.Mem.Col2.AdT.CosShape

set_option maxHeartbeats 1600000 in
open Classical in

theorem cosShape : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → ∀ (u : B.Word) (a : I.ι) (i : ℕ) (p : PtAt B.R I.sel (I.tup a) (I.cst a) u i) (P : SBof I a), (i + 1 ≠ B.R.m → cosetIn p P = ∅) ∧ (i + 1 = B.R.m → (cosetIn p P).Nonempty ∧ (∀ y ∈ p.1.2, (frsF I.sel (I.tup a) p.1.1 P).symm y ∈ cosetIn p P) ∧ ∀ z ∈ cosetIn p P, (∀ z', z' ∈ cosetIn p P ↔ GlobalTheory.TwU.SameCoset I.sel (I.tup a) (I.cst a) P z' z) ∧ ∀ g g' : Sp B.fields.E (B.R.N i) ≃ₗ[B.fields.E] Sp B.fields.E (B.R.N i), g' ∈ Formalism.L2.Col.GLint B.fields.E (B.R.N i) P.1 → CongE P.1 ((I.cst a).D P) g g' → GlobalTheory.TwU.SameCoset I.sel (I.tup a) (I.cst a) P (g z) z → ∀ z', g' z' ∈ cosetIn p P ↔ z' ∈ cosetIn p P) := by
  intro B X I hI u a i p P
  refine ⟨fun hi => ?_, fun hi => ?_⟩
  ·
    have h0 : p.1.2 = ∅ := by
      have h := p.2
      rw [ysAt_ys_of_ne (h := hi)] at h
      exact Set.mem_singleton_iff.mp h
    ext z
    simp [cosetIn, h0]
  · obtain ⟨y₀, hy₀, hYeq⟩ := PtAt.mem_ybSet p hi

    have hfr : ∀ x, (frsF I.sel (I.tup a) p.1.1 P) x ∈ Formalism.HermitianLatticesTheory.localization₂ P.1.asIdeal p.1.1.deco.1.N ↔
        x ∈ stdAt B.fields.E (B.R.N i) P.1 := by
      intro x
      simp only [frsF]
      split_ifs with h
      · exact (GlobalTheory.TopStep.liftFr_spec p.1.1.deco.2 ⟨P.1, h⟩).1 x
      · exact p.1.1.2 ⟨P.1, (Finset.mem_union.mp P.2).resolve_left h⟩ x
    have hF : ∀ w ∈ Formalism.HermitianLatticesTheory.localization₂ P.1.asIdeal p.1.1.deco.1.N,
        (frsF I.sel (I.tup a) p.1.1 P).symm w ∈ stdAt B.fields.E (B.R.N i) P.1 := by
      intro w hw
      rw [← hfr, LinearEquiv.apply_symm_apply]
      exact hw
    have hc : ((qOf P.1 : ℕ) : B.fields.E) ≠ 0 := by
      exact_mod_cast (GlobalTheory.GO.ChRoot.qOf_pos P.1).ne'
    have hpow : ∀ (S : Submodule (𝓞 B.fields.E) (Sp B.fields.E (B.R.N i))) (k : ℕ) (x : Sp B.fields.E (B.R.N i)),
        x ∈ S → ((qOf P.1 : ℕ) : B.fields.E) ^ k • x ∈ S := by
      intro S k x hx
      have h := pow_smul_mem S ((qOf P.1 : ℕ) : 𝓞 B.fields.E) k hx
      simpa using h
    have hY0 : y₀ ∈ p.1.2 := by
      rw [hYeq, Set.mem_setOf_eq, sub_self]
      exact zero_mem _
    have hY1 := (mem_locLat _ _ _ _).1 hy₀ P
    have hGL : ∀ g' : Sp B.fields.E (B.R.N i) ≃ₗ[B.fields.E] Sp B.fields.E (B.R.N i),
        g' ∈ Formalism.L2.Col.GLint B.fields.E (B.R.N i) P.1 →
          ∀ x, g' x ∈ stdAt B.fields.E (B.R.N i) P.1 ↔ x ∈ stdAt B.fields.E (B.R.N i) P.1 := by
      intro g' hg'
      exact hg'
    by_cases hP : P.1 ∈ (B.primes X).vGs
    ·
      have hYl : ∀ y ∈ p.1.2, (((qOf P.1 : ℕ) : B.fields.E) ^ 0)⁻¹ • (y - y₀) ∈ Formalism.HermitianLatticesTheory.localization₂ P.1.asIdeal p.1.1.deco.1.N := by
        intro y hy
        rw [hYeq, Set.mem_setOf_eq] at hy
        have h := (mem_locLat _ _ _ _).1 hy P
        simpa [hP] using h
      have hy₀' : ((qOf P.1 : ℕ) : B.fields.E) ^ 1 • y₀ ∈ Formalism.HermitianLatticesTheory.localization₂ P.1.asIdeal p.1.1.deco.1.N := by
        simpa [hP] using hY1
      have hC : ∀ z, z ∈ cosetIn p P ↔ ∃ y ∈ p.1.2,
          (((qOf P.1 : ℕ) : B.fields.E) ^ 0)⁻¹ • (z - (frsF I.sel (I.tup a) p.1.1 P).symm y) ∈
            stdAt B.fields.E (B.R.N i) P.1 := by
        intro z
        simp only [cosetIn, Set.mem_setOf_eq, if_pos hP]
      have hSC : ∀ x y : Sp B.fields.E (B.R.N i), GlobalTheory.TwU.SameCoset I.sel (I.tup a) (I.cst a) P x y ↔
          (((qOf P.1 : ℕ) : B.fields.E) ^ 0)⁻¹ • (x - y) ∈ stdAt B.fields.E (B.R.N i) P.1 := by
        intro x y
        rw [GlobalTheory.GO.ChRoot.mem_stdAt']
        simp only [GlobalTheory.TwU.SameCoset, if_pos hP, Pi.smul_apply, smul_eq_mul]
      obtain ⟨k1, k2, k3⟩ := core (stdAt B.fields.E (B.R.N i) P.1) (Formalism.HermitianLatticesTheory.localization₂ P.1.asIdeal p.1.1.deco.1.N)
        (frsF I.sel (I.tup a) p.1.1 P) hF _ hc hpow p.1.2 y₀ 0 1 hY0 hYl hy₀' (cosetIn p P) hC
      refine ⟨k1, k2, fun z hz => ⟨fun z' => ((k3 z hz).1 z').trans (hSC z' z).symm, ?_⟩⟩
      intro g g' hg' hcong hgz z'
      have hD1 := (hI.idx_ok a).depthG P hP
      exact (k3 z hz).2 g g' _ (hGL g' hg') hcong (by omega) ((hSC _ _).1 hgz) z'
    ·
      have hYl : ∀ y ∈ p.1.2, (((qOf P.1 : ℕ) : B.fields.E) ^ (I.cst a).M)⁻¹ • (y - y₀) ∈
          Formalism.HermitianLatticesTheory.localization₂ P.1.asIdeal p.1.1.deco.1.N := by
        intro y hy
        rw [hYeq, Set.mem_setOf_eq] at hy
        have h := (mem_locLat _ _ _ _).1 hy P
        simpa [hP] using h
      have hy₀' : ((qOf P.1 : ℕ) : B.fields.E) ^ (I.cst a).M • y₀ ∈ Formalism.HermitianLatticesTheory.localization₂ P.1.asIdeal p.1.1.deco.1.N := by
        simpa [hP] using hY1
      have hC : ∀ z, z ∈ cosetIn p P ↔ ∃ y ∈ p.1.2,
          (((qOf P.1 : ℕ) : B.fields.E) ^ (I.cst a).M)⁻¹ • (z - (frsF I.sel (I.tup a) p.1.1 P).symm y) ∈
            stdAt B.fields.E (B.R.N i) P.1 := by
        intro z
        simp only [cosetIn, Set.mem_setOf_eq, if_neg hP]
      have hSC : ∀ x y : Sp B.fields.E (B.R.N i), GlobalTheory.TwU.SameCoset I.sel (I.tup a) (I.cst a) P x y ↔
          (((qOf P.1 : ℕ) : B.fields.E) ^ (I.cst a).M)⁻¹ • (x - y) ∈ stdAt B.fields.E (B.R.N i) P.1 := by
        intro x y
        rw [GlobalTheory.GO.ChRoot.mem_stdAt']
        simp only [GlobalTheory.TwU.SameCoset, if_neg hP, Pi.smul_apply, smul_eq_mul]
      obtain ⟨k1, k2, k3⟩ := core (stdAt B.fields.E (B.R.N i) P.1) (Formalism.HermitianLatticesTheory.localization₂ P.1.asIdeal p.1.1.deco.1.N)
        (frsF I.sel (I.tup a) p.1.1 P) hF _ hc hpow p.1.2 y₀ (I.cst a).M (I.cst a).M hY0 hYl hy₀' (cosetIn p P) hC
      refine ⟨k1, k2, fun z hz => ⟨fun z' => ((k3 z hz).1 z').trans (hSC z' z).symm, ?_⟩⟩
      intro g g' hg' hcong hgz z'
      have hD2 := (hI.idx_ok a).depthQ P hP
      exact (k3 z hz).2 g g' _ (hGL g' hg') hcong (by omega) ((hSC _ _).1 hgz) z'

end GlobalTheory.Mem.Col2.AdT.CosShape
