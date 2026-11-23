import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BlockUniOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TangentFrameAtIntegralPoint
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsEquivOfIsGrpPullback

set_option autoImplicit false

noncomputable section

open NumberField CategoryTheory AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.BasicNotions Formalism.MainNotions Formalism.DegreeFormula Formalism.L2.Pj GlobalTheory GlobalTheory.ArInt GlobalTheory.VB GlobalTheory.CovTest GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.Toroidal GlobalTheory.ArLieBase
open GlobalTheory.TwoLat GlobalTheory.OrthFilt GlobalTheory.VdmRec GlobalTheory.TrueGeo
open GlobalTheory.LieVB (omega)
open GlobalTheory.LocM (tanEv)
open Formalism.MainNotions.DIV.Cons (intO)
open scoped Classical
open GlobalTheory.LieFilt

namespace GlobalTheory.LieFilt

section SlopeTestRemainingChoices

open ReciprocityTheory.ChartRestriction.G.PullbackSections

attribute [local instance] Over.cartesianMonoidalCategory

theorem isCombAtG_eq {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
    {X : Scheme.{0}} {t : SAB H X} {K : Type} [CommRing K] {x : Sp K ⟶ X} {m : ℕ}
    {u : Fin m → (Sp (DualNumber K) ⟶ t.G.left)} {a : Fin m → K} {w w' : Sp (DualNumber K) ⟶ t.G.left}
    (h : IsCombAtG t x u a w) (h' : IsCombAtG t x u a w') : w = w' := by
  obtain ⟨p, hp, hp'⟩ := h
  obtain ⟨q, hq, hq'⟩ := h'
  have e : p = q := by
    funext i
    exact Over.OverMorphism.ext ((hp i).trans (hq i).symm)
  rw [← hp', ← hq', e]

theorem sum_sigma_block {ι : Type} [Fintype ι] {r : ι → ℕ} {M : Type} [AddCommMonoid M]
    (f : (Σ τ, Fin (r τ)) → M) (τ : ι) (hf : ∀ s : Σ τ, Fin (r τ), s.1 ≠ τ → f s = 0) :
    ∑ s, f s = ∑ j, f ⟨τ, j⟩ := by
  rw [Fintype.sum_sigma]
  exact Finset.sum_eq_single τ (fun τ' _ h => Finset.sum_eq_zero fun j _ => hf ⟨τ', j⟩ h) (by simp)

end SlopeTestRemainingChoices

section Main

open ReciprocityTheory.ChartRestriction.G.PullbackSections MonoidalCategory CartesianMonoidalCategory MonObj

attribute [local instance] Over.cartesianMonoidalCategory

theorem grCond_tanMat_of_inGr : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
    {Dw : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Datum H} {l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H}
    {Xo : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Moduli Dw l} {c : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Coeff l} {Oz : Type} [CommRing Oz]
    {β : Oz →+* c.F} (Z : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Model Xo c β) {C : Type} [NontriviallyNormedField C] [IsUltrametricDist C] (φ : c.F →+* C)
    (xO : Sp ↥(intO C) ⟶ Z.X) (x : Sp C ⟶ Z.X), spMap (intO C).subtype ≫ xO = x →
    ∀ {g : ℕ} (ch : VB.Chart (omega Z.t.G) g), ⊤ ≤ xO ⁻¹ᵁ ch.U →
    ∀ {r : (E →+* ℂ) → ℕ} (u : ∀ τ, Fin (r τ) → (Sp (DualNumber C) ⟶ Z.t.G.left)), (∀ τ, IsEigBasis Z φ x τ (u τ)) →
    (∀ τ w, IsEigTan Z φ x τ w →
      ((∃ a : Fin (r τ) → C, (∀ i, ‖a i‖ ≤ 1) ∧ IsCombAtG Z.t x (u τ) a w) ↔ InGr Z φ x (latDR Z.t x) τ w)) →
    ∀ P : Matrix (Fin g) (Σ τ, Fin (r τ)) C, IsTanMat Z x ch (fun s : Σ τ, Fin (r τ) => u s.1 s.2) P →
    GrCond (fun s : Σ τ, Fin (r τ) => (Fintype.equivFin (E →+* ℂ) s.1 : ℕ)) P := by
  intro E _ _ _ H Dw l Xo c Oz _ β Z C _ _ φ xO x hx g ch hO r u hu hG P hPm
  have : IsProper Z.s := projProper _ _ _ Z.proj
  have hsep : Z.X.IsSeparated := ⟨by rw [← Limits.terminal.comp_from Z.s]; infer_instance⟩
  have hV : ⊤ ≤ x ⁻¹ᵁ ch.U := by
    subst hx
    exact fun q _ => hO (Set.mem_univ (spMap (intO C).subtype q))
  obtain ⟨Φ, hΦ⟩ := GlobalTheory.LocM.TanPair.exists_tanM_equiv _ _ _ Z.t C x ch.U hV g ch.e ch.isFrame
  let U : (Σ τ, Fin (r τ)) → TanM x Z.t.G := fun s => LieMet.tanOf ((hu s.1).1 s.2).1
  have hUe : ∀ (s : Σ τ, Fin (r τ)) (o : 𝓞 E), actR Z.t.act o (U s) = φ (embK c s.1 o) • U s :=
    fun s o => LieMet.tan_ext (((hu s.1).1 s.2).2 o)
  have hP : ∀ s b, P b s = Φ (U s) b := fun s b => (hPm s ((hu s.1).1 s.2).1 hV b).trans (hΦ (U s) b).symm
  have hcomb : ∀ d : (Σ τ, Fin (r τ)) → C, Φ (∑ s, d s • U s) = P.mulVec d := fun d => by
    funext b
    simp only [map_sum, map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Matrix.mulVec, dotProduct, hP]
    exact Finset.sum_congr rfl fun s _ => mul_comm _ _
  have hlat : ∀ v : TanM x Z.t.G, (tv v).left ∈ latDR Z.t x ↔ ∀ b, ‖Φ v b‖ ≤ 1 := fun v =>
    (GlobalTheory.TanSec.Norm.mem_latDR_iff_tanEv Z.t hsep hx hO hV ch.isFrame (LieMet.isTan_tv v)).trans
      (forall_congr' fun b => by rw [hΦ]; rfl)
  have heig : ∀ (τ : E →+* ℂ) {n : ℕ} (d : Fin n → C) (V : Fin n → TanM x Z.t.G),
      (∀ i (o : 𝓞 E), actR Z.t.act o (V i) = φ (embK c τ o) • V i) → IsEigTan Z φ x τ (tv (∑ i, d i • V i)).left :=
    fun τ n d V hV' => by
      refine ⟨LieMet.isTan_tv _, fun o => ?_⟩
      have e3 : actR Z.t.act o (∑ i, d i • V i) = φ (embK c τ o) • ∑ i, d i • V i := by
        simp only [map_sum, map_smul, hV', Finset.smul_sum]
        exact Finset.sum_congr rfl fun j _ => smul_comm _ _ _
      exact congrArg (fun z => (tv z).left) e3
  intro k a ha
  by_cases hk : ∃ τ, (Fintype.equivFin (E →+* ℂ) τ : ℕ) = k
  · obtain ⟨τ, rfl⟩ := hk
    have ha' : ∀ s : Σ τ, Fin (r τ), s.1 ≠ τ → a s = 0 := fun s h =>
      ha s fun h' => h ((Fintype.equivFin _).injective (Fin.ext h'))
    have hWτ : ∑ s, a s • U s = ∑ j, a ⟨τ, j⟩ • U ⟨τ, j⟩ :=
      sum_sigma_block (fun s => a s • U s) τ fun s h => by rw [ha' s h, zero_smul]
    have hWe : IsEigTan Z φ x τ (tv (∑ s, a s • U s)).left := by
      rw [hWτ]
      exact heig τ _ _ fun j o => hUe ⟨τ, j⟩ o
    have hWc : IsCombAtG Z.t x (u τ) (fun j => a ⟨τ, j⟩) (tv (∑ s, a s • U s)).left :=
      (LieMet.isComb_iff (fun j => U ⟨τ, j⟩) _ _).2 hWτ
    have h1 : (∀ z, ‖a z‖ ≤ 1) ↔ ∃ a'' : Fin (r τ) → C, (∀ i, ‖a'' i‖ ≤ 1) ∧
        IsCombAtG Z.t x (u τ) a'' (tv (∑ s, a s • U s)).left := by
      constructor
      · intro h
        exact ⟨fun j => a ⟨τ, j⟩, fun j => h _, hWc⟩
      · rintro ⟨a'', h'', hc⟩ z
        by_cases hz : z.1 = τ
        · obtain ⟨z1, z2⟩ := z
          dsimp only at hz
          subst hz
          have e := ((hu z1).2 _ hWe).unique hc hWc
          rw [← congrFun e z2]
          exact h'' z2
        · rw [ha' z hz, norm_zero]
          exact zero_le_one
    rw [h1, hG τ _ hWe]
    constructor
    · rintro ⟨m, ρ, v, hv, w', hw', hc⟩
      have hexp : ∀ i, ∃ e : (Σ τ, Fin (r τ)) → C, (∀ s : Σ τ, Fin (r τ), s.1 ≠ ρ i → e s = 0) ∧
          LieMet.tanOf (hv i).2.1 = ∑ s, e s • U s := fun i => by
        obtain ⟨b, hb, -⟩ := (hu (ρ i)).2 (v i) (hv i).2
        have hb' := (LieMet.isComb_iff (fun j => U ⟨ρ i, j⟩) b (LieMet.tanOf (hv i).2.1)).1 hb
        refine ⟨fun s => if h : s.1 = ρ i then b (Fin.cast (congrArg r h) s.2) else 0,
          fun s hs => dif_neg hs, ?_⟩
        rw [sum_sigma_block _ (ρ i) fun s hs => by simp only [dif_neg hs, zero_smul], hb']
        exact Finset.sum_congr rfl fun j _ => by dsimp only; rw [dif_pos rfl]; rfl
      choose e he1 he2 using hexp
      let V : Fin m → TanM x Z.t.G := fun i => LieMet.tanOf (hv i).2.1
      refine ⟨∑ i, e i, fun s hs => ?_, ?_⟩
      · rw [Finset.sum_apply]
        refine Finset.sum_eq_zero fun i _ => he1 i s fun h => hs ?_
        show (Fintype.equivFin (E →+* ℂ) s.1 : ℕ) < Fintype.equivFin (E →+* ℂ) τ
        rw [h]
        exact (hv i).1
      · have hfam : (fun i => (tv ((Fin.cons (∑ s, a s • U s) V : Fin (m + 1) → TanM x Z.t.G) i)).left) =
            (Fin.cons (tv (∑ s, a s • U s)).left v : Fin (m + 1) → _) := by
          funext i
          refine Fin.cases ?_ (fun j => ?_) i <;> rfl
        have hc' := (LieMet.isComb_iff (Fin.cons (∑ s, a s • U s) V) (fun _ => 1)
          ((∑ s, a s • U s) + ∑ i, V i)).2 (by simp [Fin.sum_univ_succ])
        rw [hfam] at hc'
        have hw'eq := isCombAtG_eq hc hc'
        have hsum : (∑ s, a s • U s) + ∑ i, V i = ∑ s, (a + ∑ i, e i) s • U s := by
          simp only [V, he2, Pi.add_apply, Finset.sum_apply, add_smul, Finset.sum_smul, Finset.sum_add_distrib]
          rw [Finset.sum_comm]
        intro b
        rw [← hcomb, ← hsum]
        exact (hlat _).1 (hw'eq ▸ hw') b
    · rintro ⟨a', ha'1, ha'2⟩
      let S := {ρ : E →+* ℂ // (Fintype.equivFin (E →+* ℂ) ρ : ℕ) < Fintype.equivFin (E →+* ℂ) τ}
      let ρ : Fin (Fintype.card S) → (E →+* ℂ) := fun i => ((Fintype.equivFin S).symm i).1
      let V : Fin (Fintype.card S) → TanM x Z.t.G := fun i => ∑ j, a' ⟨ρ i, j⟩ • U ⟨ρ i, j⟩
      have hVs : ∑ i, V i = ∑ s, a' s • U s := by
        let p : (E →+* ℂ) → Prop := fun ρ' => (Fintype.equivFin (E →+* ℂ) ρ' : ℕ) < Fintype.equivFin (E →+* ℂ) τ
        have h0 : ∑ ρ' : {ρ' // ¬ p ρ'}, ∑ j, a' ⟨ρ'.1, j⟩ • U ⟨ρ'.1, j⟩ = 0 :=
          Finset.sum_eq_zero fun ρ' _ => Finset.sum_eq_zero fun j _ => by rw [ha'1 ⟨ρ'.1, j⟩ ρ'.2, zero_smul]
        rw [Fintype.sum_sigma, ← Fintype.sum_subtype_add_sum_subtype p
          (fun ρ' => ∑ j, a' ⟨ρ', j⟩ • U ⟨ρ', j⟩), h0, add_zero]
        exact ((Fintype.equivFin S).symm.sum_comp (fun ρ' : S => ∑ j, a' ⟨ρ'.1, j⟩ • U ⟨ρ'.1, j⟩))
      refine ⟨Fintype.card S, ρ, fun i => (tv (V i)).left,
        fun i => ⟨((Fintype.equivFin S).symm i).2, heig _ _ _ fun j o => hUe ⟨ρ i, j⟩ o⟩,
        (tv ((∑ s, a s • U s) + ∑ i, V i)).left, ?_, ?_⟩
      · rw [hlat, hVs, ← Finset.sum_add_distrib]
        simp only [← add_smul]
        intro b
        have := hcomb (a + a')
        simp only [Pi.add_apply] at this
        rw [this]
        exact ha'2 b
      · have hfam : (fun i => (tv ((Fin.cons (∑ s, a s • U s) V : Fin (Fintype.card S + 1) → TanM x Z.t.G) i)).left) =
            (Fin.cons (tv (∑ s, a s • U s)).left (fun i => (tv (V i)).left) : Fin (Fintype.card S + 1) → _) := by
          funext i
          refine Fin.cases ?_ (fun j => ?_) i <;> rfl
        have hc' := (LieMet.isComb_iff (Fin.cons (∑ s, a s • U s) V) (fun _ => 1)
          ((∑ s, a s • U s) + ∑ i, V i)).2 (by simp [Fin.sum_univ_succ])
        rwa [hfam] at hc'
  · have ha0 : a = 0 := funext fun s => ha s fun h => hk ⟨s.1, h⟩
    subst ha0
    refine iff_of_true (fun z => by simp) ⟨0, fun _ _ => rfl, fun b => by simp⟩

end Main

end GlobalTheory.LieFilt

end
