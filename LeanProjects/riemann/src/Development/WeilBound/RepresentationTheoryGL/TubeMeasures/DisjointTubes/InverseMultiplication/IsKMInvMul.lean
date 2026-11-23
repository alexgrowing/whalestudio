import Development.WeilBound.RepresentationTheoryGL.TubeMeasures.DisjointTubes.TubeSt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRepsModKM

open NumberField IsDedekindDomain MeasureTheory Matrix GlobalTheory.AdLat GlobalTheory.UCls GlobalTheory.SUVol ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Up
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.StandardLattice Formalism.IndefR.Lev Formalism.IndefR.Datum GlobalTheory.AdelicScalar
open GlobalTheory.CovTop.VolUp
open scoped ENNReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace MainStatements.Tam.I

open GlobalTheory.UCls.IdxK

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]

theorem isKM_inv_mul' {n M : ℕ} {c : E ≃ₐ[F] E} {G : Matrix (Fin n) (Fin n) E} {L : Set (Fin n → E)}
    {g s : Matrix (Fin n) (Fin n) (RA F E)} (hg : GlobalTheory.UCls.IsKM c G L 1 g) (hs : GlobalTheory.UCls.IsKM c G L 1 s)
    (hgs : ∀ x ∈ GlobalTheory.AdLat.hat F L, ∃ y ∈ GlobalTheory.AdLat.hat F L, g *ᵥ x - s *ᵥ x = M • y) :
    GlobalTheory.UCls.IsKM c G L M (s⁻¹ * g) := by
  have hsu : IsUnit s.det := hs.1.1
  have hss : ∀ v, s *ᵥ (s⁻¹ *ᵥ v) = v := fun v => by
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hsu, Matrix.one_mulVec]
  have hss' : ∀ v, s⁻¹ *ᵥ (s *ᵥ v) = v := fun v => by
    rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hsu, Matrix.one_mulVec]
  have into : ∀ x ∈ GlobalTheory.AdLat.hat F L, s *ᵥ x ∈ GlobalTheory.AdLat.hat F L := by
    intro x hx
    obtain ⟨y, hy, h⟩ := hs.2.1 x hx
    rw [one_smul] at h
    rw [show s *ᵥ x = x + y by rw [← h]; abel]
    exact add_mem hx hy
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
  · rw [Matrix.det_mul, Matrix.det_nonsing_inv]
    exact (hsu.ringInverse).mul hg.1.1
  · intro x y
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, ← hs.1.2 (s⁻¹ *ᵥ (g *ᵥ x)) (s⁻¹ *ᵥ (g *ᵥ y)), hss, hss,
      hg.1.2]
  · intro x hx
    obtain ⟨y, hy, h⟩ := hgs x hx
    obtain ⟨w, hw, rfl⟩ := hs.2.2 y hy
    refine ⟨w, hw, ?_⟩
    have h1 : g *ᵥ x = s *ᵥ (x + M • w) := by
      rw [Matrix.mulVec_add, Matrix.mulVec_smul, ← h]; abel
    rw [← Matrix.mulVec_mulVec, h1, hss']
    abel
  · intro x hx
    obtain ⟨y, hy, h⟩ := hg.2.2 (s *ᵥ x) (into x hx)
    exact ⟨y, hy, by rw [← Matrix.mulVec_mulVec, h, hss']⟩

end MainStatements.Tam.I

namespace MainStatements.Tam

open GlobalTheory.UCls.IdxK

theorem idx : IdxSt := by
  intro E _ _ _ r M G Λ hM hSD
  classical
  have hFG : Λ.FG := hSD.2.2.1
  obtain ⟨e, heΛ, he⟩ := GlobalTheory.T.exists_gens_mod_nsmul_of_fg_numberField E r M Λ hM hFG
  obtain ⟨T, hTc, hTΛ, hT⟩ := GlobalTheory.T.exists_reps_mod_lattice_card_le E r M Λ hM hFG
  have hLo : ∀ o : 𝓞 E, ∀ x ∈ (Λ : Set (Fin r → E)), o • x ∈ (Λ : Set (Fin r → E)) :=
    fun o x hx => Λ.smul_mem o hx
  have hLb : ∀ b : 𝓞 (maximalRealSubfield E), ∀ x ∈ (Λ : Set (Fin r → E)),
      algebraMap (maximalRealSubfield E) E (b : maximalRealSubfield E) • x ∈ (Λ : Set (Fin r → E)) := by
    intro b x hx
    have hi : IsIntegral ℤ (algebraMap (maximalRealSubfield E) E (b : maximalRealSubfield E)) :=
      b.2.map (IsScalarTower.toAlgHom ℤ (maximalRealSubfield E) E)
    exact Λ.smul_mem (⟨_, hi⟩ : 𝓞 E) hx
  have hQ : ∀ z ∈ GlobalTheory.AdLat.hat (maximalRealSubfield E) (Λ : Set (Fin r → E)), ∃ t ∈ T,
      ∃ y ∈ GlobalTheory.AdLat.hat (maximalRealSubfield E) (Λ : Set (Fin r → E)), z = GlobalTheory.AdLat.fv _ t + M • y := by
    intro z hz
    obtain ⟨t0, ht0, y0, hy0, rfl⟩ := hat_approx hM hLb Λ.zero_mem (fun x hx y hy => Λ.add_mem hx hy)
      (fun x hx => Λ.neg_mem hx) z hz
    obtain ⟨t, ht, y1, hy1, rfl⟩ := hT t0 ht0
    refine ⟨t, ht, GlobalTheory.AdLat.fv _ y1 + y0, add_mem (fv_mem hy1) hy0, ?_⟩
    rw [fv_add, fv_nsmul, smul_add, add_assoc]
  have into : ∀ g, GlobalTheory.UCls.IsKM (IsCMField.complexConj E) G (Λ : Set (Fin r → E)) 1 g →
      ∀ x ∈ GlobalTheory.AdLat.hat (maximalRealSubfield E) (Λ : Set (Fin r → E)),
        g *ᵥ x ∈ GlobalTheory.AdLat.hat (maximalRealSubfield E) (Λ : Set (Fin r → E)) := by
    intro g hg x hx
    obtain ⟨y, hy, h⟩ := hg.2.1 x hx
    rw [one_smul] at h
    rw [show g *ᵥ x = x + y by rw [← h]; abel]
    exact add_mem hx hy
  let K1 := {g : Matrix (Fin r) (Fin r) (RA (maximalRealSubfield E) E) //
    GlobalTheory.UCls.IsKM (IsCMField.complexConj E) G (Λ : Set (Fin r → E)) 1 g}
  have hex : ∀ g : K1, ∀ i, ∃ t ∈ T, ∃ y ∈ GlobalTheory.AdLat.hat (maximalRealSubfield E) (Λ : Set (Fin r → E)),
      g.1 *ᵥ GlobalTheory.AdLat.fv _ (e i) = GlobalTheory.AdLat.fv _ t + M • y :=
    fun g i => hQ _ (into g.1 g.2 _ (fv_mem (heΛ i)))
  choose τ hτT yy hyy hτ using hex
  let σ : (Fin r → Fin r → E) → Matrix (Fin r) (Fin r) (RA (maximalRealSubfield E) E) :=
    fun t => if h : ∃ g : K1, τ g = t then h.choose.1 else 1
  refine ⟨(Fintype.piFinset fun _ : Fin r => T).image σ, ?_, ?_⟩
  · calc _ ≤ (Fintype.piFinset fun _ : Fin r => T).card := Finset.card_image_le
      _ = T.card ^ r := by simp
      _ ≤ (M ^ (2 * fdeg E * r)) ^ r := Nat.pow_le_pow_left hTc r
      _ = _ := by rw [← pow_mul]; ring_nf
  · intro g hg
    let g' : K1 := ⟨g, hg⟩
    have hex' : ∃ g'' : K1, τ g'' = τ g' := ⟨g', rfl⟩
    have hσ : σ (τ g') = hex'.choose.1 := dif_pos hex'
    have hsτ : τ hex'.choose = τ g' := hex'.choose_spec
    set s' := hex'.choose with hs'
    refine ⟨s'.1, Finset.mem_image.2 ⟨τ g', Fintype.mem_piFinset.2 fun i => hτT g' i, hσ⟩, s'.2,
      s'.1⁻¹ * g, ?_, ?_⟩
    · refine MainStatements.Tam.I.isKM_inv_mul' hg s'.2 ?_
      refine cong_of_gens hLo e he g s'.1 (into g hg) (into s'.1 s'.2) fun i => ?_
      refine ⟨yy g' i - yy s' i, sub_mem (hyy g' i) (hyy s' i), ?_⟩
      have h1 := hτ g' i
      have h2 := hτ s' i
      rw [hsτ] at h2
      change g *ᵥ GlobalTheory.AdLat.fv _ (e i) = _ at h1
      rw [h1, h2, smul_sub]
      abel
    · rw [← mul_assoc, Matrix.mul_nonsing_inv _ s'.2.1.1, one_mul]

end MainStatements.Tam

end
