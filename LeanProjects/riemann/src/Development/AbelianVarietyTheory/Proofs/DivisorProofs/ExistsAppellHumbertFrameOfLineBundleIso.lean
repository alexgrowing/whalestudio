import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAHOfIsFactorAH
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.ValAtLem
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped Matrix

namespace GlobalTheory.TransportFrame

open ReciprocityTheory.ChartRestriction.G.TB.ValAt

variable {X : Scheme.{0}}

theorem pspec_eq (p q : PrimeSpectrum ℂ) : p = q :=
  PrimeSpectrum.ext ((Ideal.eq_bot_of_prime p.asIdeal).trans (Ideal.eq_bot_of_prime q.asIdeal).symm)

theorem chart_pt (L : LB X) (hL : L.IsLB) (y : Sp ℂ ⟶ X) : ∃ j, ⊤ ≤ y ⁻¹ᵁ L.U j := by
  let p0 : Sp ℂ := (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum ℂ)
  have hmem : y p0 ∈ (⨆ i, L.U i : X.Opens) := by rw [hL.cover]; trivial
  obtain ⟨j, hj⟩ := TopologicalSpace.Opens.mem_iSup.mp hmem
  refine ⟨j, fun q _ => ?_⟩
  have : q = p0 := pspec_eq q p0
  rw [this]
  exact hj

theorem val_res_unit (x : Sp ℂ ⟶ X) {U V : X.Opens} (hVU : V ≤ U) (h : ⊤ ≤ x ⁻¹ᵁ V) (a : Γ(X, U)ˣ) :
    valAt' x V (res hVU a : Γ(X, V)) = valAt' x U (a : Γ(X, U)) :=
  ReciprocityTheory.ChartRestriction.G.TB.ValAt.valAt'_res x hVU h (a : Γ(X, U))

theorem val_inv_unit (x : Sp ℂ ⟶ X) (U : X.Opens) (h : ⊤ ≤ x ⁻¹ᵁ U) (a : Γ(X, U)ˣ) :
    valAt' x U ((a⁻¹ : Γ(X, U)ˣ) : Γ(X, U)) = (valAt' x U (a : Γ(X, U)))⁻¹ :=
  map_units_inv (valHom x U h) a

theorem val_unit_ne (x : Sp ℂ ⟶ X) (U : X.Opens) (h : ⊤ ≤ x ⁻¹ᵁ U) (a : Γ(X, U)ˣ) :
    valAt' x U (a : Γ(X, U)) ≠ 0 :=
  (a.isUnit.map (valHom x U h)).ne_zero

theorem val_gen {L L' : LB X} (w : LB.Iso L' L) (hw : w.IsGen) (x : Sp ℂ ⟶ X) (i i₂ : L.ι) (j j₂ : L'.ι)
    (h₁ : ⊤ ≤ x ⁻¹ᵁ (L.U i ⊓ L'.U j)) (h₂ : ⊤ ≤ x ⁻¹ᵁ (L.U i₂ ⊓ L'.U j₂)) :
    valAt' x (L.U i ⊓ L'.U j) (w.s (i, j)).val =
      valAt' x (L.U i ⊓ L.U i₂) (L.g i i₂).val * (valAt' x (L'.U j ⊓ L'.U j₂) (L'.g j j₂).val)⁻¹ *
        valAt' x (L.U i₂ ⊓ L'.U j₂) (w.s (i₂, j₂)).val := by
  have hW : ⊤ ≤ x ⁻¹ᵁ ((L.U i ⊓ L'.U j) ⊓ (L.U i₂ ⊓ L'.U j₂)) := fun p hp => ⟨h₁ hp, h₂ hp⟩
  have E : res (show L.U i ⊓ L'.U j ⊓ (L.U i₂ ⊓ L'.U j₂) ≤ L.U i ⊓ L'.U j from inf_le_left)
      (w.s (i, j) : Γ(X, L.U i ⊓ L'.U j)ˣ) =
      (res (show L.U i ⊓ L'.U j ⊓ (L.U i₂ ⊓ L'.U j₂) ≤ L.U i ⊓ L.U i₂ from
          le_inf (inf_le_left.trans inf_le_left) (inf_le_right.trans inf_le_left)) (L.g i i₂) *
        (res (show L.U i ⊓ L'.U j ⊓ (L.U i₂ ⊓ L'.U j₂) ≤ L'.U j ⊓ L'.U j₂ from
          le_inf (inf_le_left.trans inf_le_right) (inf_le_right.trans inf_le_right)) (L'.g j j₂))⁻¹) *
      res (show L.U i ⊓ L'.U j ⊓ (L.U i₂ ⊓ L'.U j₂) ≤ L.U i₂ ⊓ L'.U j₂ from inf_le_right)
        (w.s (i₂, j₂) : Γ(X, L.U i₂ ⊓ L'.U j₂)ˣ) := hw (i, j) (i₂, j₂)
  have e := congrArg (fun a : Γ(X, (L.U i ⊓ L'.U j) ⊓ (L.U i₂ ⊓ L'.U j₂))ˣ =>
    valAt' x _ (a : Γ(X, (L.U i ⊓ L'.U j) ⊓ (L.U i₂ ⊓ L'.U j₂)))) E
  simp only [Units.val_mul, ReciprocityTheory.ChartRestriction.G.TB.ValAt.valAt'_mul, val_inv_unit x _ hW, val_res_unit x _ hW] at e
  have a1 := val_res_unit x (show L.U i ⊓ L'.U j ⊓ (L.U i₂ ⊓ L'.U j₂) ≤ L.U i ⊓ L'.U j from inf_le_left) hW
    (w.s (i, j) : Γ(X, L.U i ⊓ L'.U j)ˣ)
  have a2 := val_res_unit x (show L.U i ⊓ L'.U j ⊓ (L.U i₂ ⊓ L'.U j₂) ≤ L.U i₂ ⊓ L'.U j₂ from inf_le_right) hW
    (w.s (i₂, j₂) : Γ(X, L.U i₂ ⊓ L'.U j₂)ˣ)
  exact a1.symm.trans (e.trans (congrArg (fun t => _ * t) a2))

end GlobalTheory.TransportFrame

namespace GlobalTheory.TransportFrame

open ReciprocityTheory.ChartRestriction.G.TB.ValAt

theorem val_g_self {X : Scheme.{0}} {L : LB X} (hL : L.IsLB) (x : Sp ℂ ⟶ X) (i : L.ι) (h : ⊤ ≤ x ⁻¹ᵁ L.U i) :
    valAt' x (L.U i ⊓ L.U i) (L.g i i).val = 1 := by
  have e := val_res_unit x (le_inf le_rfl le_rfl : L.U i ≤ L.U i ⊓ L.U i) h (L.g i i)
  rw [hL.g_self i, Units.val_one, ReciprocityTheory.ChartRestriction.G.TB.ValAt.valAt'_one x _ h] at e
  exact e.symm

variable {A : Over (Sp ℂ)} [GrpObj A] {g : ℕ} {L L' : LB A.left}

def chartOf (hL' : L'.IsLB) (y : Sp ℂ ⟶ A.left) : L'.ι := (chart_pt L' hL' y).choose

theorem chartOf_spec (hL' : L'.IsLB) (y : Sp ℂ ⟶ A.left) : ⊤ ≤ y ⁻¹ᵁ L'.U (chartOf hL' y) :=
  (chart_pt L' hL' y).choose_spec

def frT (u' : HolUnif A L' g) (hL' : L'.IsLB) (w : LB.Iso L' L) (i : L.ι) (z : Fin g → ℂ) : ℂ :=
  valAt' (u'.ex z).left (L.U i ⊓ L'.U (chartOf hL' (u'.ex z).left)) (w.s (i, chartOf hL' (u'.ex z).left)).val *
    u'.fr (chartOf hL' (u'.ex z).left) z

theorem frT_eq (u' : HolUnif A L' g) (hL : L.IsLB) (hL' : L'.IsLB) (w : LB.Iso L' L) (hw : w.IsGen) (i : L.ι) (j : L'.ι)
    (z : Fin g → ℂ) (hi : ⊤ ≤ (u'.ex z).left ⁻¹ᵁ L.U i) (hj : ⊤ ≤ (u'.ex z).left ⁻¹ᵁ L'.U j) :
    frT u' hL' w i z = valAt' (u'.ex z).left (L.U i ⊓ L'.U j) (w.s (i, j)).val * u'.fr j z := by
  have h0 := chartOf_spec hL' (u'.ex z).left
  have hij0 : ⊤ ≤ (u'.ex z).left ⁻¹ᵁ (L.U i ⊓ L'.U (chartOf hL' (u'.ex z).left)) := fun p hp => ⟨hi hp, h0 hp⟩
  have hij : ⊤ ≤ (u'.ex z).left ⁻¹ᵁ (L.U i ⊓ L'.U j) := fun p hp => ⟨hi hp, hj hp⟩
  have h0j : ⊤ ≤ (u'.ex z).left ⁻¹ᵁ (L'.U (chartOf hL' (u'.ex z).left) ⊓ L'.U j) := fun p hp => ⟨h0 hp, hj hp⟩
  have G := val_gen w hw (u'.ex z).left i i (chartOf hL' (u'.ex z).left) j hij0 hij
  have C := u'.fr_compat (chartOf hL' (u'.ex z).left) j z h0j
  have hne := val_unit_ne (u'.ex z).left _ h0j (L'.g (chartOf hL' (u'.ex z).left) j)
  have hs := val_g_self hL (u'.ex z).left i hi
  unfold frT
  rw [G, hs, C]
  have hc := inv_mul_cancel₀ hne
  linear_combination (valAt' (u'.ex z).left (L.U i ⊓ L'.U j) (w.s (i, j)).val * u'.fr j z) * hc

theorem frT_hol (u' : HolUnif A L' g) (hL : L.IsLB) (hL' : L'.IsLB) (w : LB.Iso L' L) (hw : w.IsGen) (i : L.ι) :
    DifferentiableOn ℂ (frT u' hL' w i) {z | ⊤ ≤ (u'.ex z).left ⁻¹ᵁ L.U i} := by
  intro z0 hz0
  obtain ⟨j, hj⟩ := chart_pt L' hL' (u'.ex z0).left
  have hT := u'.hol (L.U i ⊓ L'.U j) (w.s (i, j)).val
  have hz0' : ⊤ ≤ (u'.ex z0).left ⁻¹ᵁ L.U i := hz0
  have hz0T : z0 ∈ {z | ⊤ ≤ (u'.ex z).left ⁻¹ᵁ (L.U i ⊓ L'.U j)} :=
    show ⊤ ≤ (u'.ex z0).left ⁻¹ᵁ (L.U i ⊓ L'.U j) from fun p hp => ⟨hz0' hp, hj hp⟩
  have hd : DifferentiableOn ℂ (fun z => valAt' (u'.ex z).left (L.U i ⊓ L'.U j) (w.s (i, j)).val * u'.fr j z)
      {z | ⊤ ≤ (u'.ex z).left ⁻¹ᵁ (L.U i ⊓ L'.U j)} :=
    hT.2.mul ((u'.fr_hol j).mono fun z (hz : ⊤ ≤ (u'.ex z).left ⁻¹ᵁ (L.U i ⊓ L'.U j)) p hp => (hz hp).2)
  have hev : frT u' hL' w i =ᶠ[nhds z0]
      fun z => valAt' (u'.ex z).left (L.U i ⊓ L'.U j) (w.s (i, j)).val * u'.fr j z :=
    Filter.eventually_of_mem (hT.1.mem_nhds hz0T) fun z (hz : ⊤ ≤ (u'.ex z).left ⁻¹ᵁ (L.U i ⊓ L'.U j)) =>
      frT_eq u' hL hL' w hw i j z (fun p hp => (hz hp).1) (fun p hp => (hz hp).2)
  exact (((hd z0 hz0T).differentiableAt (hT.1.mem_nhds hz0T)).congr_of_eventuallyEq hev).differentiableWithinAt

theorem frT_ne (u' : HolUnif A L' g) (hL : L.IsLB) (hL' : L'.IsLB) (w : LB.Iso L' L) (hw : w.IsGen) (i : L.ι)
    (z : Fin g → ℂ) (hi : ⊤ ≤ (u'.ex z).left ⁻¹ᵁ L.U i) : frT u' hL' w i z ≠ 0 := by
  obtain ⟨j, hj⟩ := chart_pt L' hL' (u'.ex z).left
  rw [frT_eq u' hL hL' w hw i j z hi hj]
  have hij : ⊤ ≤ (u'.ex z).left ⁻¹ᵁ (L.U i ⊓ L'.U j) := fun p hp => ⟨hi hp, hj hp⟩
  exact mul_ne_zero (val_unit_ne _ _ hij (w.s (i, j) : Γ(A.left, L.U i ⊓ L'.U j)ˣ)) (u'.fr_ne j z hj)

theorem frT_compat (u' : HolUnif A L' g) (hL : L.IsLB) (hL' : L'.IsLB) (w : LB.Iso L' L) (hw : w.IsGen) (i i₂ : L.ι)
    (z : Fin g → ℂ) (h : ⊤ ≤ (u'.ex z).left ⁻¹ᵁ (L.U i ⊓ L.U i₂)) :
    frT u' hL' w i z = valAt' (u'.ex z).left (L.U i ⊓ L.U i₂) (L.g i i₂).val * frT u' hL' w i₂ z := by
  obtain ⟨j, hj⟩ := chart_pt L' hL' (u'.ex z).left
  have hi : ⊤ ≤ (u'.ex z).left ⁻¹ᵁ L.U i := fun p hp => (h hp).1
  have hi₂ : ⊤ ≤ (u'.ex z).left ⁻¹ᵁ L.U i₂ := fun p hp => (h hp).2
  rw [frT_eq u' hL hL' w hw i j z hi hj, frT_eq u' hL hL' w hw i₂ j z hi₂ hj,
    val_gen w hw (u'.ex z).left i i₂ j j (fun p hp => ⟨hi hp, hj hp⟩) (fun p hp => ⟨hi₂ hp, hj hp⟩),
    val_g_self hL' (u'.ex z).left j hj]
  ring

def transport (u' : HolUnif A L' g) (hL : L.IsLB) (hL' : L'.IsLB) (w : LB.Iso L' L) (hw : w.IsGen) :
    HolUnif A L g where
  ex := u'.ex
  ex_add := u'.ex_add
  ex_onto := u'.ex_onto
  Λ := u'.Λ
  ker := u'.ker
  discrete := u'.discrete
  full := u'.full
  hol := u'.hol
  fr := frT u' hL' w
  fr_hol := frT_hol u' hL hL' w hw
  fr_ne := frT_ne u' hL hL' w hw
  fr_compat := frT_compat u' hL hL' w hw

theorem isFactorAH_transport (u' : HolUnif A L' g) (hL : L.IsLB) (hL' : L'.IsLB) (w : LB.Iso L' L) (hw : w.IsGen)
    {Hm : Matrix (Fin g) (Fin g) ℂ} {χ' : u'.Λ → ℂ} (h : GlobalTheory.TorusRM.IsFactorAH u' Hm χ') :
    GlobalTheory.TorusRM.IsFactorAH (transport u' hL hL' w hw) Hm χ' := by
  refine ⟨h.1, h.2.1, fun (l : u'.Λ) i z hz => ?_⟩
  obtain ⟨j, hj⟩ := chart_pt L' hL' (u'.ex z).left
  have he : u'.ex (z + l) = u'.ex z := by rw [u'.ex_add, (u'.ker l).2 l.2, _root_.mul_one]
  have hz0 : ⊤ ≤ (u'.ex z).left ⁻¹ᵁ L.U i := hz
  have hz' : ⊤ ≤ (u'.ex (z + l)).left ⁻¹ᵁ L.U i := he ▸ hz0
  have hj' : ⊤ ≤ (u'.ex (z + l)).left ⁻¹ᵁ L'.U j := he ▸ hj
  show frT u' hL' w i z = χ' l * Complex.exp (Real.pi * (z ⬝ᵥ Hm.mulVec (star (l : Fin g → ℂ))) +
        Real.pi / 2 * ((l : Fin g → ℂ) ⬝ᵥ Hm.mulVec (star (l : Fin g → ℂ)))) * frT u' hL' w i (z + l)
  rw [frT_eq u' hL hL' w hw i j z hz0 hj, frT_eq u' hL hL' w hw i j (z + l) hz' hj', h.2.2 l j z hj, he]
  ring

theorem exists_holUnif_isFactorAH_of_lbIso : ∀ (A : Over (Sp ℂ)) [GrpObj A] (g : ℕ) (L L' : LB A.left)
    (u' : HolUnif A L' g) (Hm : Matrix (Fin g) (Fin g) ℂ) (χ' : u'.Λ → ℂ), L.IsLB → L'.IsLB → LBIso L L' →
    GlobalTheory.TorusRM.IsFactorAH u' Hm χ' → ∃ (u : HolUnif A L g) (χ : u.Λ → ℂ), u.ex = u'.ex ∧ GlobalTheory.TorusRM.IsFactorAH u Hm χ := by
  intro A _ g L L' u' Hm χ' hL hL' hiso h
  obtain ⟨w, hw⟩ := LBIso.symm hiso
  exact ⟨transport u' hL hL' w hw, χ', rfl, isFactorAH_transport u' hL hL' w hw h⟩

end GlobalTheory.TransportFrame
