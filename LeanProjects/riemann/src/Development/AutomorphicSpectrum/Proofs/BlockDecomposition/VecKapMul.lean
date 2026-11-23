import Mathlib
import Development.WeilBound.RepresentationTheoryGL.EisensteinSeries.SiegelEisensteinHalfPlane.MirabolicGenerators.SideUnfold

noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology
open scoped NumberField.AdeleRing
open GroundTheory.Global GroundTheory.Automorphic GroundTheory.Automorphic.GodementSection
open PositivityTheory.RgEis PositivityTheory.RgEis.MG

namespace GlobalTheory.CompanionTheory.RgEisTerm

section Lin

variable {R : Type} [CommRing R] {ι : Type} [Fintype ι] [DecidableEq ι]

theorem stab_diag_mul {i : ι} {g : GL ι R} (hg : g ∈ stab R ({i} : Set ι)) :
    (g : Matrix ι ι R) i i * ((g⁻¹ : GL ι R) : Matrix ι ι R) i i = 1 := by
  have h : ((g * g⁻¹ : GL ι R) : Matrix ι ι R) i i = 1 := by simp
  rw [Units.val_mul, Matrix.mul_apply, Finset.sum_eq_single i] at h
  · exact h
  · intro b _ hb
    rw [(hg b (by simpa using hb) i rfl).2, mul_zero]
  · intro h'; exact absurd (Finset.mem_univ i) h'

theorem det_uniq {n R : Type} [CommRing R] [Unique n] [DecidableEq n] (F : Fintype n) (A : Matrix n n R) :
    @Matrix.det n _ F R _ A = A default default :=
  Matrix.det_unique A

theorem bdet_singleton {i : ι} {g : GL ι R} (hg : g ∈ stab R ({i} : Set ι)) :
    ((bdet ({i} : Set ι) g : Rˣ) : R) = (g : Matrix ι ι R) i i := by
  classical
  unfold bdet
  split_ifs with h
  · rw [IsUnit.unit_spec, det_uniq]; rfl
  · refine absurd ?_ h
    rw [det_uniq]
    exact IsUnit.of_mul_eq_one _ (stab_diag_mul hg)

theorem bdet_inv_singleton {i : ι} {g : GL ι R} (hg : g ∈ stab R ({i} : Set ι)) :
    (((bdet ({i} : Set ι) g)⁻¹ : Rˣ) : R) = ((g⁻¹ : GL ι R) : Matrix ι ι R) i i :=
  Units.inv_eq_of_mul_eq_one_right (by rw [bdet_singleton hg]; exact stab_diag_mul hg)

theorem inv_mulVec_single {i : ι} {g : GL ι R} (hg : g ∈ stab R ({i} : Set ι)) :
    ((g⁻¹ : GL ι R) : Matrix ι ι R) *ᵥ Pi.single i 1 =
      (((bdet ({i} : Set ι) g)⁻¹ : Rˣ) : R) • (Pi.single i 1 : ι → R) := by
  funext r
  rw [Matrix.mulVec_single_one, bdet_inv_singleton hg]
  by_cases h : r = i
  · subst h; simp
  · have := (hg r (by simpa using h) i rfl).2
    rw [Pi.smul_apply, Pi.single_eq_of_ne h, smul_zero]
    exact this

end Lin

section ZetaNonvanishing₂

variable {k : Type} [Field k] [NumberField k] {ι : Type} [Fintype ι] [DecidableEq ι]

theorem modPow_eq_exp (x : IdeleGroup k) (s : ℂ) :
    modPow x s = Complex.exp (s * ((adStd k).lg x : ℝ)) := by
  have hpos : (0 : ℝ) < (IdeleGroup.ideleModule k x : ℝ) := (IdeleGroup.ideleModule k x).2
  have hne : ((IdeleGroup.ideleModule k x : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hpos.ne'
  rw [modPow, Complex.cpow_def_of_ne_zero hne, ← Complex.ofReal_log hpos.le, mul_comm]
  rfl

theorem modPow_inv_neg (x : IdeleGroup k) (s : ℂ) : modPow x⁻¹ (-s) = modPow x s := by
  have h1 : modPow x⁻¹ (-s) * modPow x (-s) = 1 := by
    rw [← modPow_mul, inv_mul_cancel, modPow_one]
  have h2 : modPow x (-s) * modPow x s = 1 := by
    rw [← modPow_add, neg_add_cancel]; simp [modPow]
  calc modPow x⁻¹ (-s) = modPow x⁻¹ (-s) * (modPow x (-s) * modPow x s) := by rw [h2, mul_one]
    _ = modPow x s := by rw [← mul_assoc, h1, one_mul]

theorem lineZeta_smul (Ψ : (ι → 𝔸[k]) → ℂ) (ω : HeckeCharacter k) (s : ℂ) (u : IdeleGroup k)
    (v : ι → 𝔸[k]) :
    lineZeta Ψ ω s ((u : 𝔸[k]) • v) =
      (((ω.toIdele u)⁻¹ : Circle) : ℂ) * modPow u (-s) * lineZeta Ψ ω s v := by
  have h := globalZeta_mul_right (fun t : 𝔸[k] => Ψ (t • v)) ω s u
  simp only [lineZeta, smul_smul, mul_comm] at h ⊢
  simpa only [mul_comm] using h

theorem lineZeta_inv_smul (Ψ : (ι → 𝔸[k]) → ℂ) (ω : HeckeCharacter k) (s : ℂ) (u : IdeleGroup k)
    (v : ι → 𝔸[k]) :
    lineZeta Ψ ω s (((u⁻¹ : IdeleGroup k) : 𝔸[k]) • v) =
      (ω.toIdele u : ℂ) * modPow u s * lineZeta Ψ ω s v := by
  rw [lineZeta_smul, modPow_inv_neg, map_inv, inv_inv]

theorem lineZeta_rat (Ψ : (ι → 𝔸[k]) → ℂ) (ω : HeckeCharacter k) (s : ℂ) (x : kˣ)
    (v : ι → 𝔸[k]) :
    lineZeta Ψ ω s (algebraMap k 𝔸[k] x • v) = lineZeta Ψ ω s v := by
  have h := lineZeta_smul Ψ ω s (IdeleGroup.diagonal k x) v
  rw [IdeleGroup.coe_diagonal] at h
  rw [h, HeckeCharacter.toIdele_diagonal]
  simp [modPow, IdeleGroup.ideleModule_diagonal]

end ZetaNonvanishing₂

section Main

variable {k : Type} [Field k] [NumberField k] {ι : Type} [Fintype ι] [DecidableEq ι] {G : Type} [Group G]

theorem dgl_inv_mulVec_single (d : ι → IdeleGroup k) (i : ι) :
    (((dgl d)⁻¹ : GL ι 𝔸[k]) : Matrix ι ι 𝔸[k]) *ᵥ Pi.single i 1 =
      (((d i)⁻¹ : IdeleGroup k) : 𝔸[k]) • (Pi.single i 1 : ι → 𝔸[k]) := by
  change Matrix.diagonal (fun i => (((d i)⁻¹ : IdeleGroup k) : 𝔸[k])) *ᵥ _ = _
  funext r
  rw [Matrix.mulVec_diagonal, Pi.smul_apply, smul_eq_mul]
  by_cases h : r = i
  · subst h; rfl
  · rw [Pi.single_eq_of_ne h, mul_zero, mul_zero]

theorem dgl_mulVec_single (d : ι → IdeleGroup k) (i : ι) :
    ((dgl d : GL ι 𝔸[k]) : Matrix ι ι 𝔸[k]) *ᵥ Pi.single i 1 =
      (d i : 𝔸[k]) • (Pi.single i 1 : ι → 𝔸[k]) := by
  change Matrix.diagonal (fun i => (d i : 𝔸[k])) *ᵥ _ = _
  funext r
  rw [Matrix.mulVec_diagonal, Pi.smul_apply, smul_eq_mul]
  by_cases h : r = i
  · subst h; rfl
  · rw [Pi.single_eq_of_ne h, mul_zero, mul_zero]

theorem vec_mul (π : G →* GL ι 𝔸[k]) (d : ι → IdeleGroup k) (i : ι) {p : G} (κ : G)
    (hp : π p ∈ stab 𝔸[k] ({i} : Set ι)) :
    MG.vec (π (p * κ) * dgl d) i =
      (((bdet ({i} : Set ι) (π p) * d i)⁻¹ : IdeleGroup k) : 𝔸[k]) • MG.vec (kap π d κ) i := by
  have hinv : (π (p * κ) * dgl d)⁻¹ = (kap π d κ)⁻¹ * ((dgl d)⁻¹ * (π p)⁻¹) := by
    simp only [kap, map_mul, _root_.mul_inv_rev, inv_inv, mul_assoc, inv_mul_cancel_left, mul_inv_cancel_left]
  have hs : (((bdet ({i} : Set ι) (π p) * d i)⁻¹ : IdeleGroup k) : 𝔸[k]) =
      (((d i)⁻¹ : IdeleGroup k) : 𝔸[k]) * (((bdet ({i} : Set ι) (π p))⁻¹ : IdeleGroup k) : 𝔸[k]) := by
    rw [← Units.val_mul, _root_.mul_inv_rev]
  unfold MG.vec
  rw [hinv, Units.val_mul, Units.val_mul, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
    inv_mulVec_single hp, Matrix.mulVec_smul, dgl_inv_mulVec_single, smul_smul, Matrix.mulVec_smul, hs,
    mul_comm]

theorem vec_kap (π : G →* GL ι 𝔸[k]) (d : ι → IdeleGroup k) (i : ι) (g : G) :
    MG.vec (kap π d g) i = (d i : 𝔸[k]) • MG.vec (π g * dgl d) i := by
  have hinv : (kap π d g)⁻¹ = (π g * dgl d)⁻¹ * dgl d := by
    simp only [kap, _root_.mul_inv_rev, inv_inv, mul_assoc, inv_mul_cancel_left, inv_mul_cancel, mul_one]
  unfold MG.vec
  rw [hinv, Units.val_mul, ← Matrix.mulVec_mulVec, dgl_mulVec_single, Matrix.mulVec_smul]

theorem vec_kap_mul (π : G →* GL ι 𝔸[k]) (d : ι → IdeleGroup k) (i : ι) {r : G} (κ : G)
    (hr : π r ∈ stab 𝔸[k] ({i} : Set ι)) :
    MG.vec (kap π d (r * κ)) i =
      (((bdet ({i} : Set ι) (π r))⁻¹ : IdeleGroup k) : 𝔸[k]) • MG.vec (kap π d κ) i := by
  have hs : (d i : 𝔸[k]) * (((bdet ({i} : Set ι) (π r) * d i)⁻¹ : IdeleGroup k) : 𝔸[k]) =
      (((bdet ({i} : Set ι) (π r))⁻¹ : IdeleGroup k) : 𝔸[k]) := by
    rw [← Units.val_mul, _root_.mul_inv_rev, mul_comm (d i)⁻¹, mul_inv_cancel_comm_assoc]
  rw [vec_kap, vec_mul π d i κ hr, smul_smul, hs]

end Main

theorem term : Term := by
  intro G _ _ _ _ K _ k _ _ ι _ _ π Γ P i ω d c η S
  have hmem : ∀ p ∈ P, π p ∈ stab 𝔸[k] ({i} : Set ι) := fun p hp => (S.mem p).1 hp
  refine ⟨fun p hp κ _ => vec_mul π d i κ (hmem p hp), fun Ψ s => ⟨?_, ?_, fun x v => lineZeta_rat Ψ ω s x v⟩⟩
  · intro p hp κ _
    have hc := (S.val p hp).1
    have hη := (S.val p hp).2
    rw [vec_mul π d i κ (hmem p hp), lineZeta_inv_smul, map_mul, Circle.coe_mul, modPow_mul,
      modPow_eq_exp (bdet ({i} : Set ι) (π p)) s, hc, hη]
    simp only [zt]
    ring
  · intro r κ hr
    have hc := (S.val r hr).1
    have hη := (S.val r hr).2
    have h0 : η r = 0 := by
      have h1 := S.ht.right 1 r r.2
      have h2 := S.ht.left r hr 1
      rw [one_mul] at h1
      rw [mul_one] at h2
      linarith
    have hm : modPow (bdet ({i} : Set ι) (π r)) s = 1 := by
      rw [modPow_eq_exp, ← hη, h0]; simp
    show zt π d i Ψ ω s ((r * κ : K) : G) = c r * zt π d i Ψ ω s κ
    rw [Subgroup.coe_mul]
    simp only [zt]
    rw [vec_kap_mul π d i κ ((S.mem r).1 hr), lineZeta_inv_smul, hm, hc, mul_one]

end GlobalTheory.CompanionTheory.RgEisTerm
