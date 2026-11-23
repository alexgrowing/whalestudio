import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.LocDefs
import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.LMemMax
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.TateFin
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.DecEmb
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement

private theorem lv_gen (hP : Loc.LocalPublishedTheorems) {v l : ℕ} [Fact v.Prime] [Fact l.Prime] (hvl : v ≠ l) {H : Type} [Group H]
    [TopologicalSpace H] [IsTopologicalGroup H] (φ : H →* Formalism.BasicNotions.Loc.GQ v) (hφ : Topology.IsOpenEmbedding φ)
    (k : Type) [Field k] [Finite k] [CharP k l] [Algebra ℤ_[l] k] (κ : H →* kˣ) (hκ : IsOpen (κ.ker : Set H))
    (σ : H) (h1 : κ σ ≠ 1) (h2 : Loc.cycA v l k (φ σ) = 1) (z : H → k) (hz : IsLocallyConstant z)
    (hc : ∀ g h, z (g * h) = z g + (κ g : k) * z h) : ∃ m, ∀ g, z g = (κ g : k) * m - m := by
  letI : TopologicalSpace k := ⊥
  haveI : DiscreteTopology k := ⟨rfl⟩
  have h1' : (κ σ : k) ≠ 1 := fun h => h1 (Units.ext h)
  have hρ : ∀ g x, Loc.chRep κ g x = (κ g : k) * x := fun _ _ => rfl
  have hlc : IsLocallyConstant κ := by
    refine (IsLocallyConstant.iff_exists_open _).2 fun g => ⟨(fun h => g⁻¹ * h) ⁻¹' (κ.ker : Set H),
      hκ.preimage (continuous_const.mul continuous_id), by simp, fun h hh => ?_⟩
    have : κ (g⁻¹ * h) = 1 := hh
    rw [map_mul, map_inv, inv_mul_eq_one] at this
    exact this.symm
  have hca : ContAction (Loc.chRep κ) := by
    unfold ReciprocityTheory.Gal.ContAction
    rw [continuous_prod_of_discrete_right]
    intro y
    exact (hlc.comp fun u : kˣ => (u : k) * y).continuous
  obtain ⟨f1, f2, e1, e2⟩ := Loc.tateFin hP φ hφ k k (Loc.chRep κ) hca
  have z0 : H0 (Loc.chRep κ) = ⊥ := by
    rw [eq_bot_iff]
    intro m hm
    have := (mem_riemannRochSpace_iff_regularAt_everywhere _ _).1 hm σ
    rw [hρ] at this
    rw [Submodule.mem_bot]
    by_contra h
    exact h1' (mul_right_cancel₀ h (by rw [this, one_mul]))
  have z2 : Loc.H0dual ((Loc.cycA v l k).comp φ) (Loc.chRep κ) = ⊥ := by
    rw [eq_bot_iff]
    intro f hf
    rw [Submodule.mem_bot]
    refine LinearMap.ext fun x => ?_
    have := hf σ x
    rw [MonoidHom.comp_apply, h2, hρ, ← smul_eq_mul, map_smul, smul_eq_mul, Units.val_one] at this
    by_contra h
    exact h1' (mul_right_cancel₀ h this)
  rw [e2, z0, z2, if_neg hvl, finrank_bot, finrank_bot] at e1
  haveI : Subsingleton (H1 (Loc.chRep κ)) := Module.finrank_zero_iff.1 e1
  have hz1 : z ∈ Z1 (Loc.chRep κ) := ⟨hz.continuous, hc⟩
  have : (Submodule.Quotient.mk ⟨z, hz1⟩ : H1 (Loc.chRep κ)) = 0 := Subsingleton.elim _ _
  rw [Submodule.Quotient.mk_eq_zero, Submodule.mem_comap, mem_coboundaries1] at this
  exact this

private theorem lv_dec (hP : Loc.LocalPublishedTheorems) {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {v l : ℕ} (hv : v.Prime)
    [Fact l.Prime] (hvl : v ≠ l) (A : ValuationSubring Ω) (hA : A.valuation (v : Ω) < 1)
    (k : Type) [Field k] [Finite k] [CharP k l] [Algebra ℤ_[l] k] (κ : Dec (F := ℚ) A →* kˣ)
    (hκ : IsOpen (κ.ker : Set (Dec (F := ℚ) A))) (σ : Dec (F := ℚ) A) (h1 : κ σ ≠ 1)
    (h2 : algebraMap ℤ_[l] k (cycZ ℚ Ω l σ : ℤ_[l]ˣ) = 1) (z : Dec (F := ℚ) A → k) (hz : IsLocallyConstant z)
    (hc : ∀ g h, z (g * h) = z g + (κ g : k) * z h) : ∃ m, ∀ g, z g = (κ g : k) * m - m := by
  haveI : Fact v.Prime := ⟨hv⟩
  obtain ⟨w, hw, hAw⟩ := GlobalTheory.DecLocal.exists_place_below (p := v) (F := ℚ) A hA
  obtain ⟨j, rfl⟩ := (Loc.decEmb (F := ℚ) (Ω := Ω) (v := v)).1 A w hAw hw
  obtain ⟨φ, hφ, -, -, -, hcyc, -⟩ := ((Loc.decEmb (F := ℚ) (Ω := Ω) (v := v)).2 j).2
  refine lv_gen hP hvl φ hφ k κ hκ σ h1 (Units.ext ?_) z hz hc
  rw [← hcyc l σ] at h2
  exact h2

private theorem lv_red {O k : Type} [CommRing O] [IsLocalRing O] [Field k] (red : O →+* k)
    (hred : ∀ a ∈ maximalIdeal O, red a = 0) (a b : O) : red a = red b ↔ residue O a = residue O b := by
  rw [← sub_eq_zero, ← map_sub, ← sub_eq_zero (a := residue O a), ← map_sub, residue_eq_zero_iff]
  refine ⟨fun h => ?_, hred _⟩
  by_contra hn
  exact ((IsLocalRing.notMem_maximalIdeal.1 hn).map red).ne_zero h

theorem UpperTheory.V.GradeZeroInterpolatingElement.locVanP :
    ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} (D : Raw Ω c), D.Good → Loc.LocalPublishedTheorems → ∀ (k : Type) [Field k] [Finite k] (red : c.O →+* k), (∀ a ∈ maximalIdeal c.O, red a = 0) → ∀ γ ∈ [D.al, D.be, D.th, D.al⁻¹, D.be⁻¹, D.th⁻¹], ∀ p ∈ D.Sb, ∀ z : D.Gp p → k, IsLocallyConstant z → (∀ g h : D.Gp p, z (g * h) = z g + red (γ g : c.O) * z h) → ∃ m, ∀ g : D.Gp p, z g = red (γ g : c.O) * m - m := by
  intro Ω _ _ _ l _ c D hD hP k _ _ red hred γ hγ p hp z hz hc
  obtain ⟨f1, f2, -, -, -, -, -, -, -, -, -, fo, -⟩ := facts D hD
  obtain ⟨hpp, hpl, -, -⟩ := f1 p hp
  obtain ⟨hσ, hom, hne⟩ := f2 p (Finset.mem_insert_of_mem hp)
  have hl : l.Prime := Fact.out
  obtain ⟨i, j, hij, hγ'⟩ : ∃ i j, lamW i ≠ lamW j ∧ ∀ g, γ g * D.ps j g = D.ps i g := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hγ
    rcases hγ with rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨2, 3, by decide, fun g => by simp [Raw.ps]⟩
    · exact ⟨1, 2, by decide, fun g => by simp [Raw.ps, Raw.be]⟩
    · exact ⟨0, 3, by decide, fun g => by simp [Raw.ps]⟩
    · exact ⟨3, 2, by decide, fun g => by simp [Raw.ps]⟩
    · exact ⟨2, 1, by decide, fun g => by simp [Raw.ps, Raw.be]⟩
    · exact ⟨3, 0, by decide, fun g => by simp [Raw.ps]⟩
  have hγr : ∀ g, red (γ g : c.O) * red (D.ps j g : c.O) = red (D.ps i g : c.O) := fun g => by
    rw [← map_mul, ← Units.val_mul, hγ']
  letI : Algebra ℤ_[l] k := (red.comp (algebraMap ℤ_[l] c.O)).toAlgebra
  have hl0 : (l : k) = 0 := by
    have hloc := (dvrFacts l c.O).2.2.1
    have hm : (l : c.O) ∈ maximalIdeal c.O := by
      rw [mem_maximalIdeal, mem_nonunits_iff, ← map_natCast (algebraMap ℤ_[l] c.O), isUnit_map_iff]
      exact PadicInt.p_nonunit
    simpa using hred _ hm
  haveI : CharP k l := (CharP.charP_iff_prime_eq_zero hl).2 hl0
  let κ : D.Gp p →* kˣ := ((Units.map red.toMonoidHom).comp γ).comp (D.Gp p).subtype
  have hκ : ∀ g : D.Gp p, (κ g : k) = red (γ g : c.O) := fun _ => rfl
  have hker : D.rbar.ker.comap (D.Gp p).subtype ≤ κ.ker := by
    intro g hg
    have hg' : D.rbar g = 1 := hg
    have h1 : ∀ a, red (D.ps a g : c.O) = 1 := fun a => by
      rw [← map_one red, lv_red red hred, map_one]
      have := congrFun (congrFun hg' a) a
      simpa [Raw.rbar, Raw.r0, diagRep] using this
    refine Units.ext ?_
    have := hγr g
    rw [h1, h1, mul_one] at this
    exact this
  refine lv_dec hP hpp hpl (D.pl p) (hD.pl_over p hpp) k κ
    (Subgroup.isOpen_mono hker (fo.preimage continuous_subtype_val)) ⟨D.sg p, hσ⟩ (fun h => ?_) ?_ z hz hc
  · have h' : red (γ (D.sg p) : c.O) = 1 := congrArg Units.val h
    have := hγr (D.sg p)
    rw [h', one_mul, lv_red red hred] at this
    exact hne i j hij this.symm
  · have : red (chiO ℚ Ω l c.O (D.sg p) : c.O) = red 1 := by
      rw [lv_red red hred, map_one]
      exact (hD.om_bar _).symm.trans hom
    rw [map_one] at this
    exact this
