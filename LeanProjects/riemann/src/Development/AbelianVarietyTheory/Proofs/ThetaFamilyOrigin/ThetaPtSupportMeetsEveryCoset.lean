import Mathlib
import Development.AbelianVarietyTheory.Definitions.Degenerations.PullChartIsLB
import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.IsVVGenOfIsThetaFamily
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.ExistsIndepSections

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ZH
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ThetaSupport

open Out in

theorem isValueAt_unique {S : Scheme.{0}} {A : Over S} [GrpObj A] {L : LB A.left} {T : Over S} (hL : L.IsLB) {n : ℤ}
    {s : LB.Sec (LPow A L n T)} {w : T ⟶ A}
    {τ : LB.Gen (LB.LinComb L (Y := T.left) (K := Fin 1) (fun _ => w.left) (fun _ => n))}
    (hτ : τ.IsGen) {c c' : Γ(T.left, ⊤)} (h : IsValueAt A L n s w τ c) (h' : IsValueAt A L n s w τ c') : c = c' :=
  (EvVal.existsUnique_sec_eq_mul_gen _ (TLinPf.linComb_cover L hL _ _)
    (EvVal.pullSec L (fun _ : Fin 1 => (snd T A).left) (fun _ => n) (ptSecT A w).left
      (fun _ => w.left) (fun _ => by rw [← Over.comp_left, ptSecT, lift_snd])
      (val_le A L w) s) τ hτ).unique h h'

open ThetaCoord in

theorem exists_ne_zero_in_coset : Out.Laws → ∀ (g n N' : ℕ), 2 ≤ n → n ^ 2 ∣ N' → ∀ (K : Type) [Field K] [IsAlgClosed K] (P : Out.PolAV (Sp K)) (hg : P.g = g) (ze : Γ(Sp K, ⊤)ˣ) (lev : Out.Level P (N' ^ 2) ze) (v : (Fin (2 * g) → ZMod (N' ^ 2)) → Γ((Out.baseOver (Sp K)).left, ⊤)), Out.IsThetaPt P N' (levelPoint lev hg) v → ∀ c : Fin (2 * g) → ZMod (N' ^ 2), ∃ d : Fin (2 * g) → ZMod (N' ^ 2), v (c + n • d) ≠ 0 := by
  intro hLaw g n N' hn hdvd K _ _ P hg ze lev v hv c
  obtain ⟨k, hk⟩ := hdvd
  have ho := hv.1
  have hu := hv.2.1
  have := P.isAb.comm
  have : NeZero (N' ^ 2) := ⟨ho.pow.pos.ne'⟩
  have hK : (N' : K) ≠ 0 := by
    have := hu.map (Scheme.ΓSpecIso (CommRingCat.of K)).hom.hom
    rw [map_natCast] at this
    exact this.ne_zero
  have hnK : (n : K) ≠ 0 := fun h => hK (by rw [hk]; push_cast; rw [h]; ring)
  obtain ⟨H₁, H₂⟩ := theta_coordinates hLaw g 1 N' 1 N' (by norm_num) (by norm_num)
  obtain ⟨⟨th, t, hth, ht⟩, Hv⟩ := H₁ (Sp K) P hg ze lev v hv
  obtain ⟨-, hli, -⟩ := (H₂ K ho hK P hg ze lev).2.2 th t hth ht
  haveI : Nontrivial Γ((Out.baseOver (Spec (CommRingCat.of K))).left, ⊤) :=
    (Scheme.ΓSpecIso (CommRingCat.of K)).commRingCatIsoToRingEquiv.symm.injective.nontrivial
  have h0 : Out.SecM.ofSec P.A (t 0) ≠ 0 := by
    have := hli.ne_zero (fun _ => 0)
    have e : (fun _ : Fin (2 * g) => (((0 : Fin 1) : ℕ) : ZMod (N' ^ 2))) = 0 := funext fun _ => by simp
    simpa only [e] using this
  obtain ⟨x, hx, τ, w, hτ, hw, hw0⟩ := hLaw.goodPt K P n hn hnK (t 0) h0 (levelPoint lev hg c ^ N')
  obtain ⟨d, rfl⟩ := (pow_eq_one_iff (M := N' ^ 2) (d := n) (e := (n * k) * N')
    (by rw [sq]; nth_rewrite 1 [hk]; ring) lev hg x).1 hx
  have e : levelPoint lev hg c ^ N' * levelPoint lev hg d ^ (n * k * N') =
      levelPoint lev hg (c + n • k • d) ^ N' := by
    rw [levelPoint_eq_lab, ← mul_smul, lab_add (levelBasis_pow lev hg), lab_nsmul (levelBasis_pow lev hg), mul_pow,
      ← pow_mul]
  refine ⟨k • d, fun hz => hw0 ?_⟩
  have key := ((Hv th t hth ht).1 (c + n • k • d))
  rw [← e] at key
  obtain ⟨u, hu'⟩ := key τ hτ
  have h₁ := hu' 0
  have e₂ : thetaCoordIdx 1 N' 0 (c + n • k • d) = c + n • k • d := by
    simp [thetaCoordIdx]
  rw [e₂, hz, mul_zero] at h₁
  exact isValueAt_unique P.isLB hτ hw h₁

end GlobalTheory.ThetaSupport
