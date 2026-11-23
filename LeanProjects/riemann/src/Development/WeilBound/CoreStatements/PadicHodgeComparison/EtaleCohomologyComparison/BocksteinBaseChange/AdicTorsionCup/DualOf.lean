import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.AdicTorsionCup.GenBaseChange
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.AdicTorsionCup.GsmulZero
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.AdicTorsionCup.PowMonoTors
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.EtProps

set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 200000

noncomputable section

open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC TensorProduct

namespace CrystallineSemistableComparison.AdicCoh

variable {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)}

theorem gal_of (hI : ZIn) (M : Model l K) {r : ℕ} {Y : Fin r → Scheme.{0}}
    (j : ∀ s, Y s ⟶ GlobalTheory.Et.geom (PadicAlgCl l) M.q) (hj : IsSum j) (hint : ∀ s, IsIntegral (Y s))
    (hperm : ∀ σ : K.fixingSubgroup, ∃ (π : Equiv.Perm (Fin r)) (θ : ∀ s, Y s ≅ Y (π s)),
      ∀ s, j s ≫ GlobalTheory.Et.galMap (PadicAlgCl l) M.q (IntermediateField.fixingSubgroupEquiv K σ) = (θ s).hom ≫ j (π s))
    (htrans : ∀ s s', ∃ (σ : K.fixingSubgroup) (θ : Y s ⟶ Y s'),
      j s ≫ GlobalTheory.Et.galMap (PadicAlgCl l) M.q (IntermediateField.fixingSubgroupEquiv K σ) = θ ≫ j s')
    (n : ℕ) (gen : ∀ s, Hl l (sch.obj (Y s)) (n : ℤ) 0) (hgen : ∀ s x, ∃ c : ℤ_[l], x = c • gen s) (s s' : Fin r) :
    ∃ (σ : K.fixingSubgroup) (z : ℚ_[l]), z ≠ 0 ∧
      M.act n σ (M.toV n (extS l hI j hj _ 0 s (gen s))) = z • M.toV n (extS l hI j hj _ 0 s' (gen s')) := by
  obtain ⟨σ, c, hc⟩ := gal_step hI M j hj hint hperm htrans n gen hgen s s'
  obtain ⟨σ2, c2, hc2⟩ := gal_step hI M j hj hint hperm htrans n gen hgen s' s
  have hact : ∀ (τ : K.fixingSubgroup) (x : M.T n), M.act n τ (M.toV n x) =
      M.toV n (pullHl l (sch.map (GlobalTheory.Et.galMap (PadicAlgCl l) M.q (IntermediateField.fixingSubgroupEquiv K τ))) n 0 x) :=
    fun τ x => gen_baseChange (N := Hl l M.spc n 0) _ x
  by_cases h0 : c = 0
  · have es : extS l hI j hj _ 0 s (gen s) = 0 := pull_gal_inj M n _ _ (by rw [hc, h0]; exact zero_smul _ _)
    have es' : extS l hI j hj _ 0 s' (gen s') = 0 := pull_gal_inj M n _ _ (by rw [hc2, es]; exact gen_smul_zero _)
    refine ⟨σ, 1, one_ne_zero, ?_⟩
    rw [hact, hc, h0, es', one_smul]
    exact congrArg (M.toV n) (zero_smul _ _)
  · refine ⟨σ, algebraMap ℤ_[l] ℚ_[l] c, ?_, ?_⟩
    · exact (map_ne_zero_iff _ (IsFractionRing.injective ℤ_[l] ℚ_[l])).2 h0
    · rw [hact, hc, toV_smul]

theorem dual_of (hI : ZIn) (M : Model l K) (hM : M.Good) (d : ℕ) (hc : M.Conn d) (hg : M.Geo) : M.Dual d := by
  obtain ⟨r, Y, j, hj, hint, hperm, htrans⟩ := hg
  refine ⟨fun i hi => ?_, fun i j' hij => ?_⟩
  · have hs : ∀ x : M.T i, x = 0 := fun x => sum_inj l hI j hj i 0 x fun s => by
      have := hint s
      have := (AdicGeo.comp_str hM hc j hj s).1
      have := (AdicGeo.comp_str hM hc j hj s).2
      exact (hl_vanish l hI (j s ≫ AdicGeo.str M) d (i : ℤ) (by exact_mod_cast hi)).elim _ _
    refine ⟨fun v w => ?_⟩
    obtain ⟨c, x, rfl⟩ := Adic.tmul_surj v
    obtain ⟨c', x', rfl⟩ := Adic.tmul_surj w
    rw [hs x, hs x', tmul_zero, tmul_zero]
  · have hgen : ∀ s, ∃ g : Hl l (sch.obj (Y s)) ((i + j' : ℕ) : ℤ) 0, ∀ x, ∃ c : ℤ_[l], x = c • g := fun s => by
      have := hint s
      have := (AdicGeo.comp_str hM hc j hj s).1
      have := (AdicGeo.comp_str hM hc j hj s).2
      exact hl_cyclic l hI (j s ≫ AdicGeo.str M) d _ (by push_cast; exact_mod_cast hij)
    choose gen hgen using hgen
    exact ⟨r, fun s => M.toV (i + j') (extS l hI j hj _ 0 s (gen s)), gen_span hI M j hj _ gen hgen,
      fun s s' => gal_of hI M j hj hint hperm htrans _ gen hgen s s',
      dual_span hI M hM d hc j hj hint i j' hij gen hgen⟩

end CrystallineSemistableComparison.AdicCoh

namespace CrystallineSemistableComparison

theorem adic : LAdicCoefficientPassage := by
  intro hI l _ K G hG hC hGeo
  exact { cup_ex := fun M _ _ x y => AdicCoh.cup_ex hI M x y
          fin := fun M hM j => AdicCoh.fin_of hI M (hG M hM) j
          dual := fun M hM d hc => AdicCoh.dual_of hI M (hG M hM) d hc (hGeo M hM d hc)
          comp := fun M hM => AdicCoh.comp_of hI G hG hC M hM }

end CrystallineSemistableComparison
