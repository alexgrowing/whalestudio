import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsAuxiliaryVectorWittDec
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.LineLatAt
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FinitePartTraceCharacterIdempotentInverseDiffere
import Formalism.LocalToGlobal.IndefiniteReal.DoubleCosetOperators.HkSplit

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin
open GlobalTheory.FinPl (latMul colMul)
open GlobalTheory.SeeSaw (idV idV_mono)

namespace GlobalTheory.StairCols

variable {D : D7}

theorem exists_coord {A B : HSp D} {c : ℕ} {ε : D.host.E} (d : HermitianOrthogonalExtensionData A B c ε) (p : Fin c) (hp : p.rev ≠ p) :
    ∃ l : Fin B.rank → D.host.E, (∀ i, ∑ k, l k * frameMat B A d.ι k i = 0) ∧
      ∀ q, ∑ k, l k * d.a k q = if q = p then 1 else 0 := by
  classical

  have hσ : ∀ x : D.host.E, (D.sp.cm.sig : D.host.E →+* D.host.E) ((D.sp.cm.sig : D.host.E →+* D.host.E) x) = x := by
    intro x
    exact star_star x
  have hG : Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) B.gram = B.gram := by
    ext i j
    exact B.herm.eq (B.frame j) (B.frame i)
  have hmul : ∀ {m n q : ℕ} (M : Matrix (Fin m) (Fin n) D.host.E) (N : Matrix (Fin n) (Fin q) D.host.E),
      Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) (M * N) =
        Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) N * Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) M := by
    intro m n q M N
    simp only [Formalism.UG.cT, Matrix.map_mul, Matrix.transpose_mul]
  have hinv : ∀ {m n : ℕ} (M : Matrix (Fin m) (Fin n) D.host.E),
      Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) (Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) M) = M := by
    intro m n M
    ext i j
    simp only [Formalism.UG.cT, Matrix.transpose_apply, Matrix.map_apply, hσ]

  have hperp : Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) d.a * B.gram * frameMat B A d.ι = 0 := by
    have h := congrArg (Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E)) d.perp
    rw [hmul, hmul, hinv, hG] at h
    rw [Matrix.mul_assoc, h]
    ext i j
    simp [Formalism.UG.cT]
  refine ⟨fun k => (Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) d.a * B.gram) p.rev k, fun i => ?_, fun q => ?_⟩
  · have h := congrFun (congrFun hperp p.rev) i
    rw [Matrix.mul_apply, Matrix.zero_apply] at h
    exact h
  · have h := congrFun (congrFun d.gram p.rev) q
    rw [Matrix.mul_apply] at h
    refine h.trans ?_
    show (if p.rev.1 + q.1 + 1 = c then (if p.rev = q then ε else (1 : D.host.E)) else 0) = _
    by_cases hq : q = p
    · rw [hq]
      have hc : p.rev.1 + p.1 + 1 = c := by
        rw [Fin.val_rev]
        have := p.isLt
        omega
      rw [if_pos hc, if_neg hp, if_pos rfl]
    · have hne : ¬ (p.rev.1 + q.1 + 1 = c) := by
        intro hs
        apply hq
        apply Fin.ext
        rw [Fin.val_rev] at hs
        have := p.isLt
        have := q.isLt
        omega
      rw [if_neg hne, if_neg hq]

theorem coord_apply {A B : HSp D} {c : ℕ} {ε : D.host.E} (d : HermitianOrthogonalExtensionData A B c ε) (p : Fin c) (l : Fin B.rank → D.host.E)
    (h0 : ∀ i, ∑ k, l k * frameMat B A d.ι k i = 0) (h1 : ∀ q, ∑ k, l k * d.a k q = if q = p then 1 else 0)
    (z : Fin A.rank → D.host.E) (u : Fin c → D.host.E) :
    ∑ k, l k * (frameMat B A d.ι *ᵥ z + d.a *ᵥ u) k = u p := by

  have swap : ∀ {n : ℕ} (M : Matrix (Fin B.rank) (Fin n) D.host.E) (w : Fin n → D.host.E),
      ∑ k, l k * (M *ᵥ w) k = ∑ j, (∑ k, l k * M k j) * w j := by
    intro n M w
    simp only [Matrix.mulVec, dotProduct, Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_
    ring
  simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib, swap, h0, h1, zero_mul,
    Finset.sum_const_zero, zero_add, ite_mul, one_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true]

theorem mulVec_single_apply {m n : ℕ} (M : Matrix (Fin m) (Fin n) D.host.E) (p : Fin n) (w : D.host.E) (k : Fin m) :
    (M *ᵥ Pi.single p w) k = M k p * w := by
  simp only [Matrix.mulVec, dotProduct, Pi.single_apply, mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]

theorem incA_mul_tmul (e : D.host.E) (x : AF D.host.F) (b : D.host.E) :
    incA D e * (x ⊗ₜ[D.host.F] b) = x ⊗ₜ[D.host.F] (e * b) := by

  rw [GlobalTheory.IdeleAA.tmul_eq, GlobalTheory.IdeleAA.tmul_eq, map_mul]
  ring

theorem col_mem_imp {A B : HSp D} {c : ℕ} {ε : D.host.E} (d : HermitianOrthogonalExtensionData A B c ε) (p : Fin c) (hp : p.rev ≠ p)
    (Λ : Lat A) (𝔟 : Fin c → FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) (𝔞 : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E)
    (s : Set D.host.E) (hs : ∀ x ∈ s, x ∈ 𝔞) (v : GlobalTheory.FinPl.Pl D) (t : AE D) :
    (fun k => t * incA D (d.a k p)) ∈ latMul B s (d.lat Λ 𝔟) (· = v) → t ∈ idV (𝔞 * 𝔟 p) v := by
  intro hmem
  obtain ⟨l, h0, h1⟩ := GlobalTheory.StairCols.exists_coord d p hp

  have hφ : latMul B s (d.lat Λ 𝔟) (· = v) ≤ (idV (𝔞 * 𝔟 p) v).comap
      (AddMonoidHom.mk' (fun y : Fin B.rank → AE D => ∑ k, incA D (l k) * y k)
        (fun x y => by simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib])) := by
    apply (AddSubgroup.closure_le _).2
    rintro y ⟨α, hα, hsupp, e, he, x, hx, rfl⟩
    obtain ⟨z, hz, u, hu, rfl⟩ := hx
    simp only [SetLike.mem_coe, AddSubgroup.mem_comap, AddMonoidHom.mk'_apply]
    have hsum : ∑ k, incA D (l k) * pairA D.host.F 0 α ⊗ₜ[D.host.F] (e * (frameMat B A d.ι *ᵥ z + d.a *ᵥ u) k)
        = pairA D.host.F 0 α ⊗ₜ[D.host.F] (e * u p) := by
      simp only [GlobalTheory.StairCols.incA_mul_tmul, ← TensorProduct.tmul_sum]
      congr 1
      rw [← GlobalTheory.StairCols.coord_apply d p l h0 h1 z u, Finset.mul_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      ring
    rw [hsum]
    exact AddSubgroup.subset_closure ⟨α, hα, hsupp, e * u p, FractionalIdeal.mul_mem_mul (hs e he) (hu p), rfl⟩
  have ht := hφ hmem
  rw [AddSubgroup.mem_comap, AddMonoidHom.mk'_apply] at ht

  have hread : ∑ k, incA D (l k) * (t * incA D (d.a k p)) = t := by
    have hl := h1 p
    rw [if_pos rfl] at hl
    calc ∑ k, incA D (l k) * (t * incA D (d.a k p)) = t * incA D (∑ k, l k * d.a k p) := by
          rw [map_sum, Finset.mul_sum]
          refine Finset.sum_congr rfl fun k _ => ?_
          rw [map_mul]
          ring
      _ = t := by rw [hl, map_one, mul_one]
  rwa [hread] at ht

def lineMap {n : ℕ} (w : Fin n → AE D) : AE D →+ (Fin n → AE D) where
  toFun t := fun k => t * w k
  map_zero' := funext fun k => zero_mul _
  map_add' x y := funext fun k => add_mul _ _ _

theorem col_mem_of {A B : HSp D} {c : ℕ} {ε : D.host.E} (d : HermitianOrthogonalExtensionData A B c ε) (p : Fin c)
    (Λ : Lat A) (𝔟 : Fin c → FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) (𝔞 : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E)
    (s : Set D.host.E)
    (hs' : ∀ x ∈ 𝔞, ∃ y ∈ s, ∃ o : 𝓞 D.host.E, x = y * (o : D.host.E)) (v : GlobalTheory.FinPl.Pl D) :
    idV (𝔞 * 𝔟 p) v ≤ (latMul B s (d.lat Λ 𝔟) (· = v)).comap (lineMap fun k => incA D (d.a k p)) := by
  apply (AddSubgroup.closure_le _).2
  rintro y ⟨α, hα, hsupp, e, he, rfl⟩
  rw [SetLike.mem_coe, AddSubgroup.mem_comap]

  have key : (fun k => pairA D.host.F 0 α ⊗ₜ[D.host.F] (d.a k p * e)) ∈ latMul B s (d.lat Λ 𝔟) (· = v) := by
    refine FractionalIdeal.mul_induction_on
      (C := fun e => (fun k => pairA D.host.F 0 α ⊗ₜ[D.host.F] (d.a k p * e)) ∈ latMul B s (d.lat Λ 𝔟) (· = v))
      he ?_ ?_
    · intro x hx y hy
      obtain ⟨x', hx', o, rfl⟩ := hs' x hx
      have hoy : (o : D.host.E) * y ∈ 𝔟 p := by
        have h := Submodule.smul_mem (𝔟 p : Submodule (𝓞 D.host.E) D.host.E) o hy
        rwa [Algebra.smul_def] at h
      have hmem : d.a *ᵥ Pi.single p ((o : D.host.E) * y) ∈ d.lat Λ 𝔟 := by
        show ∃ z ∈ Λ, ∃ u : Fin c → D.host.E, (∀ q, u q ∈ 𝔟 q) ∧
          d.a *ᵥ Pi.single p ((o : D.host.E) * y) = frameMat B A d.ι *ᵥ z + d.a *ᵥ u
        refine ⟨0, Λ.zero_mem, Pi.single p ((o : D.host.E) * y), fun q => ?_, ?_⟩
        · by_cases hq : q = p
          · subst hq
            rw [Pi.single_eq_same]
            exact hoy
          · rw [Pi.single_eq_of_ne hq]
            exact (𝔟 q).zero_mem
        · rw [Matrix.mulVec_zero, zero_add]
      apply AddSubgroup.subset_closure
      refine ⟨α, hα, hsupp, x', hx', _, hmem, ?_⟩
      funext k
      rw [GlobalTheory.StairCols.mulVec_single_apply]
      congr 1
      ring
    · intro x y hx hy
      have hsum := add_mem hx hy
      convert hsum using 1
      funext k
      rw [Pi.add_apply, mul_add, TensorProduct.tmul_add]
  convert key using 1
  funext k
  show pairA D.host.F 0 α ⊗ₜ[D.host.F] e * incA D (d.a k p) = _
  rw [mul_comm, GlobalTheory.StairCols.incA_mul_tmul]

theorem col_mem_iff {A B : HSp D} {c : ℕ} {ε : D.host.E} (d : HermitianOrthogonalExtensionData A B c ε) (p : Fin c) (hp : p.rev ≠ p)
    (Λ : Lat A) (𝔟 : Fin c → FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) (𝔞 : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E)
    (s : Set D.host.E) (hs : ∀ x ∈ s, x ∈ 𝔞)
    (hs' : ∀ x ∈ 𝔞, ∃ y ∈ s, ∃ o : 𝓞 D.host.E, x = y * (o : D.host.E)) (v : GlobalTheory.FinPl.Pl D) (t : AE D) :
    (fun k => t * incA D (d.a k p)) ∈ latMul B s (d.lat Λ 𝔟) (· = v) ↔ t ∈ idV (𝔞 * 𝔟 p) v := by
  refine ⟨GlobalTheory.StairCols.col_mem_imp d p hp Λ 𝔟 𝔞 s hs v t, fun ht => ?_⟩
  exact GlobalTheory.StairCols.col_mem_of d p Λ 𝔟 𝔞 s hs' v ht

theorem idV_inv_mul (I : Ideal (𝓞 D.host.E)) (v : GlobalTheory.FinPl.Pl D) (c : 𝓞 D.host.F) (hc : c ∉ v.asIdeal)
    (hI : algebraMap (𝓞 D.host.F) (𝓞 D.host.E) c ∈ I) (𝔞 : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) :
    idV (((I : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E))⁻¹ * 𝔞) v = idV 𝔞 v := by
  have hc0 : ((c : D.host.F) : D.host.E) ≠ 0 := GlobalTheory.IdeleAA.coe_ne_zero v c hc

  have hcoe : ((algebraMap (𝓞 D.host.F) (𝓞 D.host.E) c : 𝓞 D.host.E) : D.host.E) = ((c : D.host.F) : D.host.E) := rfl
  have hcI : ((c : D.host.F) : D.host.E) ∈ (I : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) :=
    (FractionalIdeal.mem_coeIdeal _).2 ⟨_, hI, by rw [← hcoe]⟩
  have hI0 : (I : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) ≠ 0 := by
    intro h0
    rw [h0, FractionalIdeal.mem_zero_iff] at hcI
    exact hc0 hcI
  apply le_antisymm
  ·
    apply (AddSubgroup.closure_le _).2
    rintro y ⟨α, hα, hsupp, b, hb, rfl⟩
    have hcb : ((c : D.host.F) : D.host.E) * b ∈ 𝔞 := by
      have hm := FractionalIdeal.mul_mem_mul hcI hb
      rwa [← mul_assoc, mul_inv_cancel₀ hI0, one_mul] at hm
    have heq : pairA D.host.F 0 α ⊗ₜ[D.host.F] b =
        pairA D.host.F 0 (GlobalTheory.IdeleAA.gam v c * α) ⊗ₜ[D.host.F] (((c : D.host.F) : D.host.E) * b) := by
      rw [← GlobalTheory.IdeleAA.pair_scale v c α hsupp, inv_mul_cancel_left₀ hc0]
    rw [heq]
    exact AddSubgroup.subset_closure
      ⟨_, GlobalTheory.IdeleAA.gam_mul_int v c hc hα, GlobalTheory.IdeleAA.gam_mul_supp v c α, _, hcb, rfl⟩
  ·
    apply idV_mono
    intro a ha
    have h1 : (1 : D.host.E) ∈ ((I : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E))⁻¹ := by
      rw [FractionalIdeal.mem_inv_iff hI0]
      intro y hy
      rw [one_mul]
      exact FractionalIdeal.coeIdeal_le_one hy
    simpa using FractionalIdeal.mul_mem_mul h1 ha

theorem exists_mem_modulBar {T : Type} {L : LevCh D T} (P : Places L) (sc : Consts) {v : GlobalTheory.FinPl.Pl D} (hv : v ∉ P.S0) :
    ∃ c : 𝓞 D.host.F, c ∉ v.asIdeal ∧ algebraMap (𝓞 D.host.F) (𝓞 D.host.E) c ∈ P.modulBar sc := by
  classical

  have hsep : ∀ u ∈ P.S0, ∃ c : 𝓞 D.host.F, c ∈ u.asIdeal ∧ c ∉ v.asIdeal := by
    intro u hu
    have hne : u ≠ v := fun h => hv (h ▸ hu)
    by_contra hcon
    push_neg at hcon
    apply hne
    have hle : u.asIdeal ≤ v.asIdeal := fun c hc => hcon c hc
    exact HeightOneSpectrum.ext (u.isMaximal.eq_of_le v.isPrime.ne_top hle)
  choose! f hfu hfv using hsep
  refine ⟨∏ u ∈ P.S0, f u ^ P.depth sc u, ?_, ?_⟩
  ·
    intro hmem
    obtain ⟨u, hu, hpow⟩ := (Ideal.IsPrime.prod_mem_iff (hp := v.isPrime)).1 hmem
    exact hfv u hu (v.isPrime.mem_of_pow_mem _ hpow)
  ·
    have hmod : algebraMap (𝓞 D.host.F) (𝓞 D.host.E) (∏ u ∈ P.S0, f u ^ P.depth sc u) ∈ P.modul sc := by
      rw [map_prod]
      show _ ∈ ∏ u ∈ P.S0, (P.w u).asIdeal ^ P.depth sc u
      apply Ideal.prod_mem_prod
      intro u hu
      rw [map_pow]
      apply Ideal.pow_mem_pow
      have hover := P.w_over u hu
      have h1 : f u ∈ ((P.w u).under (𝓞 D.host.F)).asIdeal := by
        rw [hover]
        exact hfu u hu
      exact h1
    have hsm := Ideal.smul_mem_pointwise_smul D.host.conj _ _ hmod
    have hcoe : ∀ x : 𝓞 D.host.F,
        ((algebraMap (𝓞 D.host.F) (𝓞 D.host.E) x : 𝓞 D.host.E) : D.host.E) = ((x : D.host.F) : D.host.E) :=
      fun _ => rfl
    have hfix : ∀ x : 𝓞 D.host.F,
        D.host.conj • algebraMap (𝓞 D.host.F) (𝓞 D.host.E) x = algebraMap (𝓞 D.host.F) (𝓞 D.host.E) x := by
      intro x
      apply RingOfIntegers.ext
      show D.host.conj ((algebraMap (𝓞 D.host.F) (𝓞 D.host.E) x : 𝓞 D.host.E) : D.host.E) = _
      rw [hcoe x]
      exact GlobalTheory.IdeleAA.conj_F x
    rw [hfix] at hsm
    exact hsm

theorem wittDecompositionColumns_auxiliaryVectors {A B B₀ : HSp D} {c ρ : ℕ} {a : HermitianOrthogonalExtensionData A B c (-1)} {d : HypDec B B₀ ρ} (h : IsAuxiliaryVectorWittDec a d) (i : Fin ρ) :
    ∃ p : Fin c, p.1 = i.1 ∧ p.rev ≠ p ∧
      ∀ t, colMul d.jX i t = fun k => t * incA D ((-D.host.xi0) ^ (i.1 + 1)) * incA D (a.a k p) := by
  obtain ⟨hc, he, -⟩ := h
  have hi := i.isLt
  refine ⟨Fin.castLE (by omega) i, rfl, ?_, fun t => ?_⟩
  · intro hrev
    have hv := congrArg Fin.val hrev
    rw [Fin.val_rev, Fin.val_castLE] at hv
    omega
  · funext k
    show t * incA D (d.e k i) = _
    rw [he]
    show t * incA D ((-D.host.xi0) ^ (i.1 + 1) * a.a k _) = _
    rw [map_mul, mul_assoc]

theorem colsAt_xZero : OnStd fun {D} _ _ {sc} {G} W F => ∀ ρ (h : 2 * ρ + 2 ≤ D.R.m), ∀ v ∉ G.pl.S0, ColsAt (F.dB ρ h) (xZero (F.dJ ρ h)) (G.Λ (.grid (2 * ρ + 2) 0)) (G.Λ (.grid (2 * ρ + 1) 0)) v := by
  intro D hD T L μ0 hL sc G W M hM F hF ρ h v hv
  intro i a _ha

  obtain ⟨p, hpi, hp, hpB⟩ := GlobalTheory.StairCols.wittDecompositionColumns_auxiliaryVectors (hF.hB ρ h) i
  obtain ⟨q, hqi, hq, hqJ⟩ := GlobalTheory.StairCols.wittDecompositionColumns_auxiliaryVectors (hF.hJ ρ h) i

  have hLB : G.Λ (.grid (2 * ρ + 2) 0) = (G.colDec (2 * ρ + 2) (by omega) h).lat (G.Λ (.core (2 * ρ + 2)))
      (stairId (G.pl.stA sc) (G.pl.stAbar sc) (2 * ρ + 2 - 1)) := G.sp.colLat _ _ _
  have hLJ : G.Λ (.grid (2 * ρ + 1) 0) = (G.colDec (2 * ρ + 1) (by omega) (by omega)).lat (G.Λ (.core (2 * ρ + 1)))
      (stairId (G.pl.stA sc) (G.pl.stAbar sc) (2 * ρ + 1 - 1)) := G.sp.colLat _ _ _
  have hs1 : ∀ x ∈ ({1} : Set D.host.E), x ∈ (1 : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) := by
    intro x hx
    rw [Set.mem_singleton_iff] at hx
    rw [hx]
    exact FractionalIdeal.one_mem_one _
  have hs1' : ∀ x ∈ (1 : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E),
      ∃ y ∈ ({1} : Set D.host.E), ∃ o : 𝓞 D.host.E, x = y * (o : D.host.E) := by
    intro x hx
    obtain ⟨o, ho⟩ := (FractionalIdeal.mem_one_iff _).1 hx
    exact ⟨1, Set.mem_singleton 1, o, by rw [one_mul]; exact ho.symm⟩
  have hsA' : ∀ x ∈ D.host.AA, ∃ y ∈ {x | x ∈ D.host.AA}, ∃ o : 𝓞 D.host.E, x = y * (o : D.host.E) :=
    fun x hx => ⟨x, hx, 1, by simp⟩
  show colMul (F.dB ρ h).jX i a ∈ latMul _ {1} _ (· = v) ↔
    colMul (F.dJ ρ h).jX i a ∈ latMul _ {x | x ∈ D.host.AA} _ (· = v)
  rw [hpB, hqJ, hLB, hLJ, GlobalTheory.StairCols.col_mem_iff _ p hp _ _ 1 {1} hs1 hs1' v,
    GlobalTheory.StairCols.col_mem_iff _ q hq _ _ D.host.AA {x | x ∈ D.host.AA} (fun x hx => hx) hsA' v]

  obtain ⟨c, hc, hcm⟩ := GlobalTheory.StairCols.exists_mem_modulBar G.pl sc hv
  have hst : (1 : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) * stairId (G.pl.stA sc) (G.pl.stAbar sc) (2 * ρ + 2 - 1) p =
      ((G.pl.modulBar sc : Ideal (𝓞 D.host.E)) : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E)⁻¹ *
        (D.host.AA * stairId (G.pl.stA sc) (G.pl.stAbar sc) (2 * ρ + 1 - 1) q) := by
    have hi := i.isLt
    have hn : 2 * ρ + 2 - 1 - p.1 = (2 * ρ + 1 - 1 - q.1) + 1 := by omega
    have hpq : p.1 = q.1 := hpi.trans hqi.symm
    show 1 * ((G.pl.stA sc) ^ (2 * ρ + 2 - 1 - p.1) * ((G.pl.stAbar sc) ^ (p.1 + 1))⁻¹) =
      _ * (_ * ((G.pl.stA sc) ^ (2 * ρ + 1 - 1 - q.1) * ((G.pl.stAbar sc) ^ (q.1 + 1))⁻¹))
    rw [hn, hpq, pow_succ]
    rw [show G.pl.stA sc = D.host.AA * ((G.pl.modulBar sc : Ideal (𝓞 D.host.E)) : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E)⁻¹
      from rfl]
    ring
  rw [hst, GlobalTheory.StairCols.idV_inv_mul _ v c hc hcm]

end GlobalTheory.StairCols

end
