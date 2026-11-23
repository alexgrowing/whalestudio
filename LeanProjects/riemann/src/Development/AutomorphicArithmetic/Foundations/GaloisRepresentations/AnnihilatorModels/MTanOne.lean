import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.PulledRead
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EpsZeroPtEpsScalePt

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES
open GlobalTheory.IwLevel (InSub IsIsogDeg)
open GlobalTheory.AbDual (evc IsAdditive swap)
attribute [local instance] Ideal.Quotient.field
open UpperTheory.Gal.crystallineComparison UpperTheory.Gal.crystallineComparison.Mod

private lemma ofFn_prod_one {X : Type*} [Monoid X] {n : ℕ} (h : n = 1) (f : Fin n → X) :
    (List.ofFn f).prod = f ⟨0, by omega⟩ := by
  subst h; simp

private lemma alg_core {F κ V : Type} [CommRing F] [Field κ] [AddCommGroup V] [Module κ V] (p : ℕ) [CharP κ p]
    (T : F →+* Module.End κ V) (u : Ideal F) (α α' : F)
    (h1 : ∀ a ∈ u, a * α ∈ Ideal.span {(p : F)})
    (h2 : α + α' - 1 ∈ Ideal.span {(p : F)}) (h3 : α' ∈ u)
    (v : V) (e : ℕ) (hv : ∀ a ∈ u ^ e, T a v = 0) : ∀ a ∈ u, T a v = 0 := by
  have hp : ∀ x ∈ Ideal.span {(p : F)}, T x = 0 := by
    intro x hx
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp hx
    rw [map_mul, map_natCast]
    have hz : ((p : ℕ) : Module.End κ V) = 0 := by
      ext y
      rw [Module.End.natCast_apply, ← Nat.cast_smul_eq_nsmul κ, CharP.cast_eq_zero, zero_smul]
      rfl
    rw [hz, mul_zero]
  have key : ∀ a ∈ u, T a = T (a * α') := by
    intro a ha
    have e1 : T (a * (α + α' - 1)) = 0 := hp _ (Ideal.mul_mem_left _ _ h2)
    have e2 : T (a * α) = 0 := hp _ (h1 a ha)
    have hs : a * α' = a + a * (α + α' - 1) - a * α := by ring
    rw [hs, map_sub, map_add, e1, e2]
    simp
  intro a ha
  have step : ∀ k : ℕ, T a = T (a * α' ^ k) ∧ a * α' ^ k ∈ u ^ (k + 1) := by
    intro k
    induction k with
    | zero => simpa using ha
    | succ k ih =>
      obtain ⟨h, hm⟩ := ih
      refine ⟨?_, ?_⟩
      · rw [h, key _ (Ideal.pow_le_self (Nat.succ_ne_zero k) hm), pow_succ, _root_.mul_assoc]
      · rw [pow_succ α', ← _root_.mul_assoc, pow_succ u]
        exact Ideal.mul_mem_mul hm h3
  obtain ⟨h, hm⟩ := step e
  rw [h]
  exact hv _ (Ideal.pow_le_pow_right (Nat.le_succ e) hm)

private lemma comp_idpow {S : Scheme.{0}} {T G : Over S} [GrpObj G] (g : T ⟶ G) (n : ℕ) :
    g ≫ (𝟙 G) ^ n = g ^ n := by
  rw [MonObj.comp_pow, Category.comp_id]

private lemma tan_pow {κ : Type} [Field κ] (p : ℕ) [CharP κ p] {S : Scheme.{0}} (x : Sp κ ⟶ S) (G : Over S)
    [GrpObj G] [IsCommMonObj G] (g : epsPtR x ⟶ G) (hg : g ∈ GlobalTheory.TanPtMod.tanSub x G) (n : ℕ) (hn : p ∣ n) :
    g ^ n = 1 := by
  obtain ⟨m, rfl⟩ := hn
  have hv : (p * m) • (Additive.ofMul (⟨g, hg⟩ : GlobalTheory.TanPtMod.tanSub x G) : GlobalTheory.TanPtMod.Tan x G) = 0 := by
    rw [← Nat.cast_smul_eq_nsmul κ, Nat.cast_mul, CharP.cast_eq_zero, zero_mul, zero_smul]
  have h2 := congrArg (fun w => ((Additive.toMul w : GlobalTheory.TanPtMod.tanSub x G) : epsPtR x ⟶ G)) hv
  simpa using h2

private theorem left_one_eq_hom_comp_eta {S : Scheme.{0}} {T A : Over S} [GrpObj A] :
    Over.Hom.left (1 : T ⟶ A) = T.hom ≫ Over.Hom.left (η[A] : 𝟙_ (Over S) ⟶ A) := by
  rw [Hom.one_def, Over.comp_left]
  congr 1

private theorem left_one_algPt_dualNumber_eq_epsPtR {κ : Type} [Field κ] {A : Over (Sp κ)} [GrpObj A] :
    Over.Hom.left (1 : algPt κ (DualNumber κ) ⟶ A) = Over.Hom.left (1 : epsPtR (𝟙 (Sp κ)) ⟶ A) := by
  rw [left_one_eq_hom_comp_eta, left_one_eq_hom_comp_eta]
  simp

theorem UpperTheory.Gal.crystallineComparison.Mod.tanOne_of :
    UElt → TanOne := by
  intro hU p _ D R _ b N hm ha r w hw κ _ _ _ β hβ o e
  have i0 : Fin D.a := ⟨0, by omega⟩
  have j0 : Fin D.m := ⟨0, by omega⟩
  have hi : ∀ i j : Fin D.a, i = j := fun i j => Fin.ext (by have := i.isLt; have := j.isLt; omega)
  have hj : ∀ i j : Fin D.m, i = j := fun i j => Fin.ext (by have := i.isLt; have := j.isLt; omega)
  have hwt : w ≠ ⊤ := by
    intro h
    have h0 := hβ i0 1 (h ▸ Submodule.mem_top)
    simp at h0
  obtain ⟨α, h1, h2, h3⟩ := hU p D r w hwt hw 1
  simp only [pow_one] at h1 h2 h3
  have hρ : β b.ρ = (r : κ) := by
    have h0 := hβ i0 _ (hw (sub_mem_uIdeal D r))
    rw [map_sub, map_sub, b.t_ω, map_intCast, map_intCast, sub_eq_zero] at h0
    exact h0
  let Tm : 𝓞 D.F →+* Module.End κ (GlobalTheory.TanPtMod.Tan (𝟙 (Sp κ)) o.A) :=
    (GlobalTheory.TanPtMod.actEnd o.act).comp (algebraMap (𝓞 D.F) D.O)
  let toE : (algPt κ (DualNumber κ) ⟶ o.A) → (epsPtR (𝟙 (Sp κ)) ⟶ o.A) :=
    fun v => Over.homMk v.left (by simpa using Over.w v)
  let frE : (epsPtR (𝟙 (Sp κ)) ⟶ o.A) → (algPt κ (DualNumber κ) ⟶ o.A) :=
    fun v => Over.homMk v.left (by simpa using Over.w v)
  have eig : ∀ v : algPt κ (DualNumber κ) ⟶ o.A, Inf (TrivSqZeroExt.fstHom κ κ κ) v →
      (∃ e', KilledBy o (uIdeal D r ^ e') v) →
      IsLieEigen (OActN.toF D o.act) (𝟙 (Sp κ)) (β.comp (b.t i0)) (toE v) := by
    intro v hinf ⟨e', hk⟩
    have hmem : toE v ∈ GlobalTheory.TanPtMod.tanSub (𝟙 (Sp κ)) o.A := by
      exact (GlobalTheory.TanPtMod.mem_tanSub_iff _ _ _).2 hinf
    have hkill : ∀ a ∈ uIdeal D r ^ e', Tm a (GlobalTheory.TanPtMod.Tan.mk (toE v) hmem) = 0 := by
      intro a ha'
      apply GlobalTheory.TanPtMod.Tan.ext
      rw [GlobalTheory.TanPtMod.Tan.hom_zero]
      show toE v ≫ o.act.act (algebraMap _ _ a) = 1
      ext1
      have h4 := congrArg Over.Hom.left (hk a ha')
      rw [Over.comp_left] at h4
      rw [Over.comp_left]
      exact h4.trans left_one_algPt_dualNumber_eq_epsPtR
    have hu := alg_core p Tm (uIdeal D r) α (D.bar α) h1 h2 h3 _ e' hkill
    have hsc : IsTanScal o.act (𝟙 (Sp κ)) (algebraMap (𝓞 D.F) D.O D.ω) (β b.ρ) (toE v) := by
      refine ⟨?_, ?_⟩
      · rw [GlobalTheory.TanPtMod.mem_tanSub_iff] at hmem
        exact hmem
      · have hz := hu _ (sub_mem_uIdeal D r)
        rw [map_sub, LinearMap.sub_apply, sub_eq_zero, map_intCast] at hz
        have hz2 := congrArg GlobalTheory.TanPtMod.Tan.hom hz
        rw [Module.End.intCast_apply, ← Int.cast_smul_eq_zsmul κ, GlobalTheory.TanPtMod.Tan.hom_smul] at hz2
        rw [hρ]
        exact congrArg Over.Hom.left hz2
    obtain ⟨w', hw', hprod⟩ := o.lie κ β (𝟙 (Sp κ)) (Category.id_comp _) (toE v) hsc
    rw [ofFn_prod_one ha, hi ⟨0, _⟩ i0] at hprod
    refine ⟨hsc.1, fun c => ?_⟩
    have h5 := (hw' i0 c).2
    rw [← hprod] at h5
    exact h5
  obtain ⟨vs, hvs, huniq⟩ := o.lieRank κ (𝟙 (Sp κ)) β (Category.id_comp _) i0
  refine ⟨frE (vs j0), ⟨?_, 1, ?_⟩, ?_, ?_⟩
  · ext1
    rw [Over.comp_left, left_one_algPt_dualNumber_eq_epsPtR]
    have hm0 : vs j0 ∈ GlobalTheory.TanPtMod.tanSub (𝟙 (Sp κ)) o.A := by
      rw [GlobalTheory.TanPtMod.mem_tanSub_iff]
      exact (hvs j0).1
    have h6 := tan_pow p (𝟙 (Sp κ)) o.A (vs j0) hm0 (p ^ (e + 1)) (dvd_pow_self p (Nat.succ_ne_zero e))
    rw [← comp_idpow] at h6
    exact congrArg Over.Hom.left h6
  · intro a ha'
    rw [pow_one] at ha'
    ext1
    rw [Over.comp_left, left_one_algPt_dualNumber_eq_epsPtR]
    have hz : β (b.t i0 a) = 0 := hβ i0 a (hw ha')
    have h7 := (hvs j0).2 a
    rw [RingHom.comp_apply, hz] at h7
    have h0 := congrArg Over.Hom.left (GlobalTheory.GrpTangentPt.epsScalePt_zero_comp (𝟙 (Sp κ)) (hvs j0).1)
    rw [← h0]
    exact h7
  · exact (hvs j0).1
  · intro v ⟨_, hk⟩ hinf
    obtain ⟨c, ⟨u', hu', hprod⟩, -⟩ := huniq (toE v) (eig v hinf hk)
    rw [ofFn_prod_one hm, hj ⟨0, _⟩ j0] at hprod
    refine ⟨c j0, ?_⟩
    have h8 := hu' j0
    rw [← hprod] at h8
    exact h8
