import Mathlib
import Development.AbelianVarietyTheory.Definitions.Degenerations.LocTheta
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.UTorsSt
import Development.AbelianVarietyTheory.PublishedTheorems.SemistableReduction₂.SemistableReductionSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.TorsionEqOneOfTranslationKeepsRatios

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZH ReciprocityTheory.ChartRestriction.G.Out Classical
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.OriginFrame

variable {S : Scheme.{0}} {A : Over S} [GrpObj A] {L : LB A.left} {T : Over S} {Z : Scheme.{0}}

theorem sval_valueAt {a : ℤ} {s : LB.Sec (LPow A L a T)} {x : T ⟶ A}
    {τ : LB.Gen (LB.LinComb L (Y := T.left) (K := Fin 1) (fun _ => x.left) (fun _ => a))} {v : Γ(T.left, ⊤)}
    (H : IsValueAt A L a s x τ v) (t : Z ⟶ T.left) {z : Z} {J} (hJ : Good L z J) :
    sval (φ := fun _ : Fin 1 => (snd T A).left) (ε := fun _ => a) s (t ≫ (ptSecT A x).left) z J =
      gs t z ⊤ v * (val τ t z J).val := by
  have hy := hJ.mem (fun _ : Fin 1 => x.left) t
  rw [sval_of (φ := fun _ : Fin 1 => (snd T A).left) (ε := fun _ => a) s (t ≫ (ptSecT A x).left) z J
    (fun _ => J (t ≫ x.left)) (fun _ => by rw [Category.assoc, ← Over.comp_left, ptSecT, lift_snd])]
  refine Eq.trans ?_ ((congrArg (gs t z _) (H _)).trans ((gs_mul _ z _ hy _ _).trans
    (congrArg₂ (· * ·) (gs_res _ z _ hy _) (gs_unit _ z _ hy _))))
  exact ((gs_res _ z _ hy _).trans (gs_pull t (ptSecT A x).left z
    (LB.wchart L (fun _ : Fin 1 => (snd T A).left) (fun _ => J (t ≫ x.left))) (val_le A L x _ hy) _)).symm

theorem val_rigT (rig : LB.Gen (L.pull (eSec A))) (k : ℤ) (t : Z ⟶ T.left) {z : Z} {J} (hJ : Good L z J) :
    val (rigT A L rig T k) t z J = val rig (t ≫ T.hom) z J ^ k := by
  have hy := hJ.mem (fun _ : Fin 1 => T.hom ≫ eSec A) t
  refine (map_zpow _ _ _).trans (congrArg (· ^ k) ((gm_res _ z _ hy _).trans ?_))
  exact gm_pull t T.hom z (LB.wchart L (fun _ : PUnit => eSec A) (fun _ => J (t ≫ T.hom ≫ eSec A)))
    (rigT_le A L _ hy) _

theorem torsFrame_pow_origin (P : PolAV S) {T : Over S} {m : ℕ}
    {rig : LB.Gen (P.L.pull (eSec P.A))} {x : T ⟶ P.A} (hx : x = 1) {τ} (H : IsTorsFrame P rig m x τ)
    (t : Z ⟶ T.left) {z : Z} {J} (hJ : Good P.L z J) :
    val τ t z J ^ (m ^ 2) = val rig (t ≫ T.hom) z J ^ (m ^ 2) := by
  subst hx
  obtain ⟨-, -, β, hβ, hn, hc⟩ := H
  have q₁ := val_corr hJ hn (t ≫ T.hom)
  have q₂ := val_corr hJ hc t
  rw [val_pull hJ, val_mul hJ, val_inv] at q₁
  rw [val_mul hJ, val_pull hJ, val_rigT _ _ _ hJ] at q₂
  have p₁ : val (rigPow P.A P.L rig ((m : ℤ) ^ 2)) (t ≫ T.hom) z J = val rig (t ≫ T.hom) z J ^ ((m : ℤ) ^ 2) :=
    map_zpow _ _ _
  have p₂ : val (powFrame P.A P.L 1 τ ((m : ℤ) ^ 2)) t z J = val τ t z J ^ ((m : ℤ) ^ 2) := map_zpow _ _ _
  have q₃ : val β (t ≫ (1 : T ⟶ P.A).left) z J = _ := q₁.trans (congrArg (· * _) p₁)
  rw [p₂, q₃, zpow_one] at q₂
  rw [← zpow_natCast, ← zpow_natCast, Nat.cast_pow, q₂]
  exact inv_mul_cancel_right _ _

theorem valF_spMap_fn {R K : Type} [CommRing R] [Field K] (y : R →+* K) (a : R) :
    valF (X := (baseOver (Sp R)).left) (spMap y) ⊤ (fn a) = y a := by
  rw [valF, dif_pos (by simp)]
  have h := congrArg (fun q => q.hom a) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom y))
  have h' := congrArg (Scheme.ΓSpecIso (CommRingCat.of K)).hom.hom h
  simp only [CommRingCat.hom_comp, RingHom.comp_apply, Iso.inv_hom_id_apply] at h'
  refine Eq.trans ?_ h'.symm
  congr 1

end GlobalTheory.OriginFrame

namespace GlobalTheory

open OriginFrame ThetaScalar in

theorem basis_value_at_origin : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (K : Type) [Field K] (y₀ : S.R →+* K) (r : Sp K ⟶ (baseOver (Sp S.R) ⊗ ρ.P.A).left) (jP : ρ.P.L.ι), r ≫ (snd (baseOver (Sp S.R)) ρ.P.A).left = spMap y₀ ≫ eSec ρ.P.A → Set.range (r ≫ (snd (baseOver (Sp S.R)) ρ.P.A).left) ⊆ ρ.P.L.U jP → ∃ ξ : K, ξ ^ ((S.r * S.N) ^ 2) = 1 ∧ ∀ l, valF r _ ((ρ.s l).f (fun _ => jP)) = y₀ ⟨S.ev 0 l, S.ev_mem 0 l⟩ * (ξ * valF (spMap y₀) _ (ρ.rig.s (fun _ => jP)).val) ^ S.N := by
  intro o Ω _ _ _ S ρ K _ y₀ r jP hr hU
  have := ρ.P.isAb.comm
  have h0 : ρ.pt 0 = 1 := mul_left_cancel (a := ρ.pt 0) (by rw [← ρ.pt_add, add_zero, _root_.mul_one])
  let z : Sp K := IsLocalRing.closedPoint K
  let t : Sp K ⟶ (baseOver (Sp S.R)).left := spMap y₀
  have ht : t ≫ (baseOver (Sp S.R)).hom = spMap y₀ := Category.comp_id _
  have hz : (spMap y₀ ≫ eSec ρ.P.A) z ∈ ρ.P.L.U jP := hU ⟨z, by rw [hr]⟩
  obtain ⟨J, hJ, eJ⟩ := exists_good ρ.P.L ρ.P.isLB z (fun _ : PUnit => spMap y₀ ≫ eSec ρ.P.A) (fun _ => jP)
    (fun _ _ _ => rfl) (fun _ => hz)
  have hs : (t ≫ (ptSecT ρ.P.A (ρ.pt 0)).left) ≫ (snd (baseOver (Sp S.R)) ρ.P.A).left = spMap y₀ ≫ eSec ρ.P.A := by
    rw [Category.assoc, ← Over.comp_left, ptSecT, lift_snd, h0, ← ht, Category.assoc]; rfl
  have er : r = t ≫ (ptSecT ρ.P.A (ρ.pt 0)).left := by
    haveI : Mono (snd (baseOver (Sp S.R)) ρ.P.A).left :=
      inferInstanceAs (Mono (pullback.snd (𝟙 (Sp S.R)) ρ.P.A.hom))
    rw [← cancel_mono (snd (baseOver (Sp S.R)) ρ.P.A).left, hr, hs]
  have hp := torsFrame_pow_origin ρ.P h0 (ρ.fr_tors 0) t hJ
  rw [ht] at hp
  have m₁ : r z ∈ LB.wchart ρ.P.L (fun _ : Fin 1 => (snd (baseOver (Sp S.R)) ρ.P.A).left) (fun _ => jP) :=
    Set.mem_iInter.2 fun _ => hU ⟨z, rfl⟩
  have m₂ : (spMap y₀) z ∈ LB.wchart ρ.P.L (fun _ : PUnit => eSec ρ.P.A) (fun _ => jP) :=
    Set.mem_iInter.2 fun _ => hz
  have m₃ := hJ.mem (fun _ : Fin 1 => (ρ.pt 0).left) t
  have a₂ : toStk z (valF (spMap y₀) _ (ρ.rig.s (fun _ => jP)).val) = (val ρ.rig (spMap y₀) z J).val :=
    (toStk_valF_gs (spMap y₀) _ z m₂ _).trans ((gs_unit _ z _ m₂ _).trans
      (congrArg Units.val (val_of ρ.rig (spMap y₀) z J (fun _ => jP) (fun _ => eJ PUnit.unit)).symm))
  obtain ⟨a, ha⟩ : ∃ a : K, toStk z a = (val (ρ.fr 0) t z J).val :=
    ⟨_, (toStk_valF_gs t _ z m₃ _).trans (gs_unit _ z _ m₃ _)⟩
  generalize valF (spMap y₀) _ (ρ.rig.s (fun _ => jP)).val = b at a₂ ⊢
  have hb : b ≠ 0 := fun e => (val ρ.rig (spMap y₀) z J).ne_zero (by rw [← a₂, e, map_zero])
  have hab : a ^ ((S.r * S.N) ^ 2) = b ^ ((S.r * S.N) ^ 2) := (toStk z).injective (by
    rw [map_pow, map_pow, ha, a₂, ← Units.val_pow_eq_pow_val, ← Units.val_pow_eq_pow_val]
    exact congrArg Units.val hp)
  refine ⟨a / b, by rw [div_pow, hab, div_self (pow_ne_zero _ hb)], fun l => (toStk z).injective ?_⟩
  have hv := sval_valueAt (ρ.ev_val l 0) t hJ
  have p : val (powFrame ρ.P.A ρ.P.L (ρ.pt 0) (ρ.fr 0) S.N) t z J = val (ρ.fr 0) t z J ^ (S.N : ℤ) :=
    map_zpow _ _ _
  rw [← er, p, zpow_natCast] at hv
  replace hv := (sval_of (φ := fun _ : Fin 1 => (snd (baseOver (Sp S.R)) ρ.P.A).left) (ε := fun _ => (S.N : ℤ))
    (ρ.s l) r z J (fun _ => jP) (fun _ => by rw [hr]; exact eJ PUnit.unit)).symm.trans hv
  have a₁ := toStk_valF_gs r _ z m₁ ((ρ.s l).f (fun _ => jP))
  have a₃ := toStk_valF_gs t ⊤ z trivial (fn (⟨S.ev 0 l, S.ev_mem 0 l⟩ : S.R))
  rw [valF_spMap_fn] at a₃
  refine a₁.trans (hv.trans ?_)
  rw [div_mul_cancel₀ _ hb, map_mul, map_pow, a₃, ha, Units.val_pow_eq_pow_val]

end GlobalTheory
