import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.KchMul
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.ExistsGenericComponentPointsOffMeagre
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.PeriodCoordinatesFramesLiftTendsto

open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj GlobalTheory.ShFam GlobalTheory.LamT GlobalTheory.KeyFourth GlobalTheory.FrameUnif GlobalTheory.Reg
open scoped Matrix TensorProduct

namespace GlobalTheory.FrameLiftAt

open Topology Filter Metric in

theorem exists_selection {X Y : Type} [MetricSpace X] [PseudoMetricSpace Y] (R : X → Y → Prop) (B : Set X)
    (b₀ : X) (x₀ : Y) (hB : B ∈ 𝓝 b₀) (h0 : R b₀ x₀) (hne : ∀ b ∈ B, ∃ x, R b x)
    (hl : ∀ V ∈ 𝓝 x₀, ∀ᶠ b in 𝓝 b₀, ∃ x ∈ V, R b x) :
    ∃ f : X → Y, (∀ b ∈ B, R b (f b)) ∧ ContinuousAt f b₀ := by
  have key : ∀ b, ∃ x, (b ∈ B → R b x ∧ dist x₀ x ≤ infDist x₀ {x | R b x} + dist b b₀) ∧ (b = b₀ → x = x₀) := by
    intro b
    by_cases hb : b = b₀
    · subst hb
      exact ⟨x₀, fun _ => ⟨h0, by rw [dist_self, dist_self, add_zero]; exact infDist_nonneg⟩, fun _ => rfl⟩
    by_cases hbB : b ∈ B
    · have hp : 0 < dist b b₀ := dist_pos.2 hb
      obtain ⟨x, hx, hd⟩ := (infDist_lt_iff (x := x₀) (s := {x | R b x})
        (r := infDist x₀ {x | R b x} + dist b b₀) (hne b hbB)).1 (by linarith)
      exact ⟨x, fun _ => ⟨hx, hd.le⟩, fun h => absurd h hb⟩
    · exact ⟨x₀, fun h => absurd h hbB, fun _ => rfl⟩
  choose f hf hf0 using key
  refine ⟨f, fun b hb => (hf b hb).1, ?_⟩
  rw [ContinuousAt, hf0 b₀ rfl, Metric.tendsto_nhds]
  intro ε hε
  filter_upwards [hB, hl _ (ball_mem_nhds x₀ (half_pos hε)), ball_mem_nhds b₀ (half_pos hε)] with b hb hx hbb
  obtain ⟨x, hx, hR⟩ := hx
  have h1 := (hf b hb).2
  have h2 : infDist x₀ {x | R b x} ≤ dist x₀ x := infDist_le_dist_of_mem hR
  rw [mem_ball] at hx hbb
  rw [dist_comm] at hx ⊢
  linarith

open Topology Filter GlobalTheory.GenericFrames in

theorem exists_frame_lift : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (g : ℕ) (e : Fin g ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ)) (F : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) (fun j => Formalism.L2.PjFree.relab c σ (e j).1)) (r : ℕ) (M : ModelsOf F r) (k : Fin F.n) (T : ThetaData e F M k), Formalism.L2.PjFree.GoodEmb c σ → ModelBase M → NegXi M → ∀ (m : ℕ) (B : Set (Fin m → ℂ)) (P : (Fin m → ℂ) → ((F.Di k).La →+ (Fin g → ℂ))), IsOpen B → IsHolPeriods (F.Di k) (fun j => Formalism.L2.PjFree.relab c σ (e j).1) B P → ∀ b₀ ∈ B, ∃ x : (Fin m → ℂ) → (Fin T.m → ℂ), (∀ b ∈ B, x b ∈ T.co ⁻¹' (M.X k).dom ∧ T.Pf (T.co (x b)) = P b) ∧ ContinuousAt x b₀ := by
  intro E _ _ _ H Dw l Xo c σ g e F r M k T hσ hM hN m B P hB hP b₀ hb₀
  obtain ⟨idx, hper, -, honto⟩ := dictionary c σ e (F.Di k) (M.X k) (M.φ k) hσ (F.sig _).1 (F.sig _).2 hM.rank
    (hM.type k).1 (hM.type k).2 (hM.ef k) (fun _ => hN k)
  choose! x₁ hx₁ hr₁ using fun b (hb : b ∈ B) => honto (P b) (hP.1 b hb)
  have hBn : ∀ᶠ b in 𝓝 b₀, b ∈ B := hB.mem_nhds hb₀
  have hPf : ∀ (x : Frame (M.X k).Ψ r) b,
      (∀ a j, pc (M.X k) x (M.φ k a : Fin r → E) (idx j).1 (idx j).2 = P b a j) → T.Pf x = P b := by
    intro x b h
    ext a j
    rw [T.per, hper, h]
  have key := GlobalTheory.PeriodLift.period_lift E r (M.X k) _ (𝓝 b₀) (x₁ b₀) x₁ (hx₁ b₀ hb₀) (hBn.mono hx₁)
    (fun v hv τ i => by
      obtain ⟨a, rfl⟩ : ∃ a, (M.φ k a : Fin r → E) = v := ⟨(M.φ k).symm ⟨v, hv⟩, by simp⟩
      obtain ⟨j, hj⟩ := idx.surjective (τ, i)
      obtain ⟨rfl, rfl⟩ : τ = (idx j).1 ∧ i = (idx j).2 := by rw [hj]; exact ⟨rfl, rfl⟩
      change Tendsto (fun b => pc (M.X k) (x₁ b) (M.φ k a) _ _) _ (𝓝 (pc (M.X k) (x₁ b₀) (M.φ k a) _ _))
      rw [hr₁ b₀ hb₀]
      have hc : ContinuousAt (fun b => P b a j) b₀ :=
        (continuous_apply j).continuousAt.comp ((hP.2 a).continuousOn.continuousAt hBn)
      exact hc.tendsto.congr' (hBn.mono fun b hb => (hr₁ b hb a j).symm))
  refine exists_selection (fun b x => x ∈ T.co ⁻¹' (M.X k).dom ∧ T.Pf (T.co x) = P b) B b₀ (T.co.symm (x₁ b₀)) hBn
    ⟨by simpa using hx₁ b₀ hb₀, by rw [T.co.apply_symm_apply]; exact hPf _ _ (hr₁ b₀ hb₀)⟩
    (fun b hb => ⟨T.co.symm (x₁ b), by simpa using hx₁ b hb,
      by rw [T.co.apply_symm_apply]; exact hPf _ _ (hr₁ b hb)⟩) fun V hV => ?_
  have hV' : T.co.symm ⁻¹' V ∩ (M.X k).dom ∈ 𝓝 (x₁ b₀) :=
    inter_mem (T.co.symm.continuous.continuousAt hV) ((FourierCoefficientDomain.isOpen_dom (M.X k)).mem_nhds (hx₁ b₀ hb₀))
  filter_upwards [hBn, key _ hV'] with b hb hx
  obtain ⟨x, ⟨hxV, hxd⟩, hxx⟩ := hx
  refine ⟨T.co.symm x, hxV, by simpa using hxd, ?_⟩
  rw [T.co.apply_symm_apply]
  exact hPf _ _ fun a j => (hxx _ _ _).trans (hr₁ b hb a j)

end GlobalTheory.FrameLiftAt
