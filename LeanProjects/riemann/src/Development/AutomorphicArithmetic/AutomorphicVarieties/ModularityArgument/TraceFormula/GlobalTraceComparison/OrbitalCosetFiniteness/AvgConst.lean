import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.OrbitalCosetFiniteness.CvGelfandAlt

namespace UpperTheory.V.Z.Tf.GlobalTraceComparison.Th

private lemma avg_const {H : Type} [Group H] (c : ℂ) : GlobalTheory.BCT.avg (fun _ : H => c) = c := by
  have hS : GlobalTheory.BCT.rStab (fun _ : H => c) = ⊤ := by
    ext k
    simp [GlobalTheory.BCT.rStab]
  unfold GlobalTheory.BCT.avg
  rw [hS]
  haveI : Subsingleton (H ⧸ (⊤ : Subgroup H)) := QuotientGroup.subsingleton_quotient_top
  haveI : Unique (H ⧸ (⊤ : Subgroup H)) := Unique.mk' _
  simp [finsum_unique]

private lemma avg_orbit {G : Type} [Group G] (K : Subgroup G) (θ : G →* G) (hθ : ∀ k ∈ K, θ k ∈ K)
    (δ x : G) (h : G → ℂ) (hh : ∀ k ∈ K, ∀ y, h (k * y) = h y ∧ h (y * k) = h y) :
    GlobalTheory.BCT.avg (fun k : K => h ((x * k)⁻¹ * δ * θ (x * k))) = h (x⁻¹ * δ * θ x) := by
  have hc : (fun k : K => h ((x * k)⁻¹ * δ * θ (x * k))) = fun _ : K => h (x⁻¹ * δ * θ x) := by
    funext k
    have e : (x * (k : G))⁻¹ * δ * θ (x * k) = (k : G)⁻¹ * ((x⁻¹ * δ * θ x) * θ k) := by
      simp only [map_mul, mul_inv_rev, mul_assoc]
    rw [e, (hh _ (K.inv_mem k.2) _).1, (hh _ (hθ _ k.2) _).2]
  rw [hc, avg_const]

end UpperTheory.V.Z.Tf.GlobalTraceComparison.Th

theorem UpperTheory.V.Z.Tf.GlobalTraceComparison.Th.twLin :
    UpperTheory.V.Z.Tf.GlobalTraceComparison.Th.TwLin := by
  intro G _ _ _ K _ _ θ hθ δ hfin f g c hf hg
  let W : DoubleCoset.Quotient (GlobalTheory.BCT.twCent θ δ : Set G) (K : Set G) → ℂ := fun q =>
    (((GlobalTheory.BCT.twCent θ δ ⊓ K.map (MulAut.conj (Quotient.out q)).toMonoidHom).relIndex
      (GlobalTheory.BCT.cptPart (GlobalTheory.BCT.twCent θ δ)) : ℕ) : ℂ)
  let y : DoubleCoset.Quotient (GlobalTheory.BCT.twCent θ δ : Set G) (K : Set G) → G := fun q =>
    (Quotient.out q)⁻¹ * δ * θ (Quotient.out q)
  have form : ∀ h : G → ℂ, (∀ k ∈ K, ∀ z, h (k * z) = h z ∧ h (z * k) = h z) →
      GlobalTheory.BCT.twOrb θ K δ h = ∑ᶠ q, W q * h (y q) := by
    intro h hh
    unfold GlobalTheory.BCT.twOrb
    exact finsum_congr fun q => by rw [avg_orbit K θ hθ δ _ h hh]
  have fin : ∀ h : G → ℂ, GlobalTheory.BCT.IsHecke K h → (Function.support fun q => W q * h (y q)).Finite := by
    intro h hh
    refine (hfin _ hh.1.isCompact).subset fun q hq => ?_
    exact subset_tsupport h (right_ne_zero_of_mul hq)
  have inv : ∀ k ∈ K, ∀ z, (fun u => f u + c * g u) (k * z) = (fun u => f u + c * g u) z ∧
      (fun u => f u + c * g u) (z * k) = (fun u => f u + c * g u) z := by
    intro k hk z
    simp only [(hf.2 k hk z).1, (hf.2 k hk z).2, (hg.2 k hk z).1, (hg.2 k hk z).2, and_self]
  have fin' : (Function.support fun q => c * (W q * g (y q))).Finite :=
    (fin g hg).subset fun q hq => right_ne_zero_of_mul hq
  rw [form _ inv, form f hf.2, form g hg.2, mul_finsum _ c,
    ← finsum_add_distrib (fin f hf) fin']
  exact finsum_congr fun q => by ring
