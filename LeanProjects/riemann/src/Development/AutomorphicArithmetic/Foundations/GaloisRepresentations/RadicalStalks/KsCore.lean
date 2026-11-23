import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RadicalStalks.IsConst
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CrystallinePull2SumCup
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RadicalStalks.EpsMulSub
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RadicalStalks.CommutingSurjectivity
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorPairingSkewHodgeLagrangianStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorPolarisationPairingNondegenerateStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorCrystalActionAdjointStatement

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.ConjSeq GlobalTheory.UPel.HT GlobalTheory.UPel.HT.ES UpperTheory.Gal.Ord
open scoped TensorProduct

private theorem exists_rep {k H : Type*} [Field k] [AddCommGroup H] [Module k H] [FiniteDimensional k H]
    (φ : LinearMap.BilinForm k H) (hskew : ∀ x y, φ x y = -φ y x) (hnd : ∀ x, (∀ y, φ x y = 0) → x = 0)
    (L : H →ₗ[k] k) : ∃ α, ∀ h, φ h α = L h := by
  have hinj : Function.Injective φ.flip := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro y hy
    apply hnd
    intro h
    have this : φ h y = 0 := LinearMap.congr_fun hy h
    rw [hskew, this, neg_zero]
  have hsurj : Function.Surjective φ.flip :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank Subspace.dual_finrank_eq.symm).1 hinj
  obtain ⟨α, hα⟩ := hsurj L
  exact ⟨α, fun h => by rw [← hα]; rfl⟩

private theorem ks_core {k H C : Type*} [Field k] [AddCommGroup H] [Module k H] [CommRing C]
    (σ : C →+* Module.End k H) (bar : C → C) (χ : C →+* k) (φ : LinearMap.BilinForm k H) (Fl : Submodule k H)
    (hskew : ∀ x y, φ x y = -φ y x) (hnd : ∀ x, (∀ y, φ x y = 0) → x = 0)
    (hiso : ∀ x ∈ Fl, ∀ y ∈ Fl, φ x y = 0)
    (hadj : ∀ c x y, φ (σ c x) y = φ x (σ (bar c) y))
    (ω e : C) (T r : k) (hT : ∀ v, σ ω v + σ (bar ω) v = T • v) (hdisc : 2 * r - T ≠ 0)
    (hL1 : ∀ c h, σ c (σ e h) - χ c • σ e h ∈ Fl) (hL3 : ∀ h, σ ω (σ e h) = r • σ e h)
    (h₀ : H) (hh₀ : σ e h₀ ∉ Fl) (x : H) (hxe : σ e x = x) (α : H)
    (hα : ∀ c h, φ (σ c h) α = χ c * φ h α) (hxα : φ x α ≠ 0) :
    ∃ g : H →ₗ[k] H,
      (∀ c, ∀ u ∈ Fl, g (σ c u) - σ c (g u) ∈ Fl) ∧
      (∀ (n : ℕ) (lam : Fin n → k) (c : Fin n → C) (u : H), ∑ l, lam l * χ (c l) = 0 →
        g (∑ l, lam l • σ (c l) ((σ ω - (T - r) • 1) u)) = 0) ∧
      (∀ u ∈ Fl, ∀ v ∈ Fl, φ (g u) v + φ u (g v) = 0) ∧ g x ∉ Fl := by
  have hcomm : ∀ a b v, σ a (σ b v) = σ b (σ a v) := by
    intro a b v
    show (σ a * σ b) v = (σ b * σ a) v
    rw [← map_mul, ← map_mul, mul_comm]
  have hbar : ∀ v, σ (bar ω) v = T • v - σ ω v := by
    intro v
    rw [← hT v]
    abel
  have hzw : ∀ c, σ ω (σ c (σ e h₀)) = r • σ c (σ e h₀) := by
    intro c
    rw [hcomm, hL3 h₀, map_smul]
  have hαc : ∀ c, σ c α = χ (bar c) • α := by
    intro c
    rw [← sub_eq_zero]
    apply hnd
    intro y
    rw [map_sub, map_smul, LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul, hadj c α y,
      hskew α (σ (bar c) y), hα (bar c) y, hskew α y]
    ring
  have hwfl : ∀ c, ∀ u ∈ Fl, φ u (σ (bar c) (σ e h₀)) = χ (bar c) * φ u (σ e h₀) := by
    intro c u hu
    have h1 := hiso u hu _ (hL1 (bar c) h₀)
    rw [map_sub, map_smul, smul_eq_mul, sub_eq_zero] at h1
    exact h1
  have hxw : φ x (σ e h₀) = 0 := by
    have h1 : φ (σ ω x) (σ e h₀) = r * φ x (σ e h₀) := by
      rw [← hxe, hL3 x, hxe, map_smul, LinearMap.smul_apply, smul_eq_mul]
    have h2 : φ (σ ω x) (σ e h₀) = (T - r) * φ x (σ e h₀) := by
      rw [hadj, hbar, hL3 h₀, map_sub, map_smul, map_smul, smul_eq_mul, smul_eq_mul]
      ring
    have h3 : (2 * r - T) * φ x (σ e h₀) = 0 := by
      linear_combination h2 - h1
    exact (mul_eq_zero.1 h3).resolve_left hdisc
  have hPz : ∀ d v, φ ((σ ω - (T - r) • 1) v) (σ d (σ e h₀)) = 0 := by
    intro d v
    simp only [LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply, map_sub, map_smul,
      smul_eq_mul]
    rw [hadj, hbar, hzw, map_sub, map_smul, map_smul, smul_eq_mul, smul_eq_mul]
    ring
  have happ : ∀ u, ((φ.flip α).smulRight (σ e h₀) + (φ.flip (σ e h₀)).smulRight α) u =
      φ u α • σ e h₀ + φ u (σ e h₀) • α := fun u => rfl
  refine ⟨(φ.flip α).smulRight (σ e h₀) + (φ.flip (σ e h₀)).smulRight α, ?_, ?_, ?_, ?_⟩
  · intro c u hu
    rw [happ, happ, map_add, map_smul, map_smul, hα c u, hadj c u (σ e h₀), hwfl c u hu, hαc c]
    have key : (χ c * φ u α) • σ e h₀ + (χ (bar c) * φ u (σ e h₀)) • α -
        (φ u α • σ c (σ e h₀) + φ u (σ e h₀) • χ (bar c) • α) =
        -(φ u α • (σ c (σ e h₀) - χ c • σ e h₀)) := by
      module
    rw [key]
    exact Fl.neg_mem (Fl.smul_mem _ (hL1 c h₀))
  · intro n lam c u hsum
    rw [happ]
    have h1 : φ (∑ l, lam l • σ (c l) ((σ ω - (T - r) • 1) u)) α = 0 := by
      simp only [map_sum, LinearMap.sum_apply, map_smul, LinearMap.smul_apply, smul_eq_mul, hα]
      have e1 : ∀ l, lam l * (χ (c l) * φ ((σ ω - (T - r) • 1) u) α) =
          (lam l * χ (c l)) * φ ((σ ω - (T - r) • 1) u) α := fun l => by ring
      rw [Finset.sum_congr rfl fun l _ => e1 l, ← Finset.sum_mul, hsum, zero_mul]
    have h2 : φ (∑ l, lam l • σ (c l) ((σ ω - (T - r) • 1) u)) (σ e h₀) = 0 := by
      simp only [map_sum, LinearMap.sum_apply, map_smul, LinearMap.smul_apply, smul_eq_mul, hadj, hPz,
        mul_zero, Finset.sum_const_zero]
    rw [h1, h2, zero_smul, zero_smul, add_zero]
  · intro u _ v _
    rw [happ, happ, map_add, map_smul, map_smul, LinearMap.add_apply, LinearMap.smul_apply,
      LinearMap.smul_apply, map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul, smul_eq_mul,
      smul_eq_mul, hskew (σ e h₀) v, hskew α v]
    ring
  · rw [happ, hxw, zero_smul, add_zero]
    intro hmem
    apply hh₀
    have := Fl.smul_mem (φ x α)⁻¹ hmem
    rwa [smul_smul, inv_mul_cancel₀ hxα, one_smul] at this

theorem UpperTheory.Gal.Ord.ks :
    ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ), 3 ≤ N → N.Coprime p → D.m = 1 →
      ∀ (k : Type) [Field k] [IsAlgClosed k] (hk : (p : k) = 0) (β : R →+* k) (o : Obj b N (spMap β)) (i : Fin D.a) (w : Ideal (𝓞 D.F)) (f : ℕ),
      RingHom.ker (β.comp (b.t i)) = w → Ideal.absNorm w = p ^ f → 0 < f → ∀ π : Par p w f,
      ∀ φ : LinearMap.BilinForm k (HdR o.A), GlobalTheory.AbDual.IsCorrForm (dp0 k) (𝟙 _) o.A o.A o.P φ → ∀ x ∈ Fil o.A, hom o π.ε x = x →
      (∃ y, (∀ c, coh o c y = β (b.t i c) • y) ∧ x y ≠ 0) →
      ∃ g : HdR o.A →ₗ[k] HdR o.A, GlobalTheory.UPel.Sm.IsKS (GlobalTheory.HTCount.crysAct o) φ (Fil o.A) (GlobalTheory.HTCount.lieZ o β) g ∧ g x ∉ Fil o.A := by
  intro p _ D R _ b N hN hNp hm k _ _ hk β o i w f hw hf hf0 π φ hφ x hxF hxe hyex
  obtain ⟨y, hy, hxy⟩ := hyex
  obtain ⟨hfd, -, hskew, hiso⟩ := GlobalTheory.T.harrisTaylor_pairing_skew_hodge_lagrangian p D R b N hN hNp k (spMap β) o β rfl φ hφ
  have hnd := GlobalTheory.T.harrisTaylor_polarisation_pairing_nondegenerate p D R b N hN hNp k (spMap β) o β rfl φ hφ
  have hadj0 := GlobalTheory.T.harrisTaylor_crystal_action_adjoint p D R b N hN hNp k (spMap β) o β rfl φ hφ
  obtain ⟨hL1, ⟨h₀, hh₀, -⟩, hL3⟩ := lie p D R b N hN hNp hm k hk β o i w f hw hf hf0 π
  haveI := hfd
  let L : HdR o.A →ₗ[k] k :=
    { toFun := fun h => h y
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  obtain ⟨α, hα0⟩ := exists_rep φ hskew hnd L
  let σ : 𝓞 D.F →+* Module.End k (HdR o.A) := (GlobalTheory.HTCount.crysAct o).comp (algebraMap (𝓞 D.F) D.O)
  have hadj : ∀ c u v, φ (σ c u) v = φ u (σ (D.bar c) v) := by
    intro c u v
    have := hadj0 (algebraMap _ _ c) u v
    rwa [D.star_F, MulOpposite.unop_op] at this
  have hT : ∀ v, σ D.ω v + σ (D.bar D.ω) v = (D.tr : k) • v := by
    intro v
    have e1 : σ D.ω + σ (D.bar D.ω) = σ (D.tr : 𝓞 D.F) := by
      rw [← map_add, D.tr_eq]
    have e2 := LinearMap.congr_fun e1 v
    rw [LinearMap.add_apply, map_intCast] at e2
    rw [e2]
    simp only [Module.End.intCast_apply]
    exact (Int.cast_smul_eq_zsmul k D.tr v).symm
  have hdisc : 2 * β b.ρ - (D.tr : k) ≠ 0 := by
    haveI : CharP k p := (CharP.charP_iff_prime_eq_zero (Fact.out)).2 hk
    intro h0
    have hr := congrArg β b.ρ_root
    simp only [map_add, map_sub, map_pow, map_mul, map_intCast, map_zero] at hr
    have e3 : ((D.tr ^ 2 - 4 * D.nm : ℤ) : k) = 0 := by
      push_cast
      linear_combination (2 * β b.ρ - D.tr) * h0 - 4 * hr
    exact D.disc_p ((CharP.intCast_eq_zero_iff k p _).1 e3)
  have hα : ∀ c h, φ (σ c h) α = (β.comp (b.t i)) c * φ h α := by
    intro c h
    rw [hα0, hα0]
    show h (coh o c y) = _
    rw [hy c, map_smul, smul_eq_mul]
    rfl
  have hxα : φ x α ≠ 0 := by
    rw [hα0]
    exact hxy
  obtain ⟨g, ga, gb, gc, gd⟩ := ks_core σ D.bar (β.comp (b.t i)) φ (Fil o.A) hskew hnd hiso hadj D.ω π.ε
    (D.tr : k) (β b.ρ) hT hdisc hL1 hL3 h₀ hh₀ x hxe α hα hxα
  refine ⟨g, ⟨?_, ?_, gc⟩, gd⟩
  · intro a u hu
    obtain ⟨c, rfl⟩ := surjO p D hm a
    exact ga c u hu
  · intro z hz
    have hle : GlobalTheory.HTCount.lieZ o β ≤ (Fil o.A).comap g := by
      apply Submodule.span_le.2
      rintro z ⟨n, lam, c, y', hy', hsum, rfl⟩
      obtain ⟨u, rfl⟩ := LinearMap.mem_range.1 hy'
      exact (congrArg (· ∈ Fil o.A) (gb n lam c u (hsum i))).mpr (Fil o.A).zero_mem
    exact hle hz
