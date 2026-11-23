import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.MatrixExtendByZeroApply
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.AdmSub
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.AdmHom
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.IsCrysOfInertia
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.Z1fDescAvg

open Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc ReciprocityTheory.Gal Topology UpperTheory.V UpperTheory.V.Loc

namespace UpperTheory.V.Z.J.StepF

section Alg

variable {G E : Type} [Group G] [Field E]

private theorem mul_entry (t : G →* GL (Fin 3) E) (g h : G) (i j : Fin 3) :
    (t (g * h) : Matrix (Fin 3) (Fin 3) E) i j =
      (t g : Matrix (Fin 3) (Fin 3) E) i 0 * (t h : Matrix (Fin 3) (Fin 3) E) 0 j +
      (t g : Matrix (Fin 3) (Fin 3) E) i 1 * (t h : Matrix (Fin 3) (Fin 3) E) 1 j +
      (t g : Matrix (Fin 3) (Fin 3) E) i 2 * (t h : Matrix (Fin 3) (Fin 3) E) 2 j := by
  rw [map_mul, Units.val_mul, Matrix.mul_apply, Fin.sum_univ_three]

private noncomputable def diag (t : G →* GL (Fin 3) E)
    (ht : ∀ g i j, j < i → (t g : Matrix (Fin 3) (Fin 3) E) i j = 0) (j : Fin 3) : G →* Eˣ :=
  MonoidHom.toHomUnits
    { toFun := fun g => (t g : Matrix (Fin 3) (Fin 3) E) j j
      map_one' := by simp
      map_mul' := fun g h => by
        have h10 := fun g => ht g 1 0 (by decide)
        have h20 := fun g => ht g 2 0 (by decide)
        have h21 := fun g => ht g 2 1 (by decide)
        rw [mul_entry]
        fin_cases j <;> simp [h10, h20, h21] }

private def two (α κ : G →* Eˣ) (b : G → E) (hb : ∀ g h, b (g * h) = α g * b h + b g * κ h) :
    Representation E G (E × E) where
  toFun g :=
    { toFun := fun x => (α g * x.1 + b g * x.2, κ g * x.2)
      map_add' := fun x y => by ext <;> simp <;> ring
      map_smul' := fun a x => by ext <;> simp <;> ring }
  map_one' := by
    have h1 : b 1 = 0 := by
      have := hb 1 1
      simpa using this
    refine LinearMap.ext fun x => ?_
    simp [h1]
  map_mul' g h := by
    refine LinearMap.ext fun x => ?_
    ext <;> simp [hb] <;> ring

private theorem two_apply (α κ : G →* Eˣ) (b : G → E) (hb : ∀ g h, b (g * h) = α g * b h + b g * κ h)
    (g : G) (x : E × E) : two α κ b hb g x = (α g * x.1 + b g * x.2, κ g * x.2) := rfl

end Alg

section Cr

variable {l : ℕ} [Fact l.Prime] {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {E : Type} [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] [TopologicalSpace E]
  [IsModuleTopology ℚ_[l] E] [IsTopologicalRing E]

private theorem crOn_map (φ : G →* GQ l) (hφ : IsOpenEmbedding φ)
    {V : Type} [AddCommGroup V] [Module E V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] E V]
    [FiniteDimensional ℚ_[l] V] [TopologicalSpace V] [IsModuleTopology ℚ_[l] V] [IsTopologicalAddGroup V]
    [ContinuousConstSMul E V]
    {V' : Type} [AddCommGroup V'] [Module E V'] [Module ℚ_[l] V'] [IsScalarTower ℚ_[l] E V']
    [FiniteDimensional ℚ_[l] V'] [TopologicalSpace V'] [IsModuleTopology ℚ_[l] V'] [IsTopologicalAddGroup V']
    [ContinuousConstSMul E V'] (ρ : Representation E G V) (ρ' : Representation E G V')
    (hρ : ReciprocityTheory.Gal.ContAction ρ) (hρ' : ReciprocityTheory.Gal.ContAction ρ') (f : V →ₗ[E] V')
    (hf : ∀ g x, f (ρ g x) = ρ' g (f x)) (H : Subgroup G) (hH : IsOpen (H : Set G)) :
    (Function.Injective f → CrOn φ ρ' H → CrOn φ ρ H) ∧ (Function.Surjective f → CrOn φ ρ H → CrOn φ ρ' H) := by
  have hφH : IsOpenEmbedding (φ.comp H.subtype) := hφ.comp hH.isOpenEmbedding_subtypeVal
  have hc : Continuous fun p : H × V => ((p.1 : G), p.2) :=
    (continuous_subtype_val.comp continuous_fst).prodMk continuous_snd
  have hc' : Continuous fun p : H × V' => ((p.1 : G), p.2) :=
    (continuous_subtype_val.comp continuous_fst).prodMk continuous_snd
  have key := isCrys_isDR_sub_quot (φ.comp H.subtype) hφH (ρ.comp H.subtype : Representation E H V)
    (ρ'.comp H.subtype : Representation E H V') (hρ.comp hc) (hρ'.comp hc') (f.restrictScalars ℚ_[l])
    (fun g x => hf g x)
  exact ⟨fun h => (key.1 h).1, fun h => (key.2 h).1⟩

omit [IsTopologicalGroup G] in
private theorem cont_two (α κ : G →* Eˣ) (b : G → E) (hb : ∀ g h, b (g * h) = α g * b h + b g * κ h)
    (hα : Continuous fun g => (α g : E)) (hκ : Continuous fun g => (κ g : E)) (hbc : Continuous b) :
    ReciprocityTheory.Gal.ContAction (two α κ b hb) :=
  (((hα.comp continuous_fst).mul (continuous_fst.comp continuous_snd)).add
    ((hbc.comp continuous_fst).mul (continuous_snd.comp continuous_snd))).prodMk
    ((hκ.comp continuous_fst).mul (continuous_snd.comp continuous_snd))

private theorem core (φ : G →* GQ l) (hφ : IsOpenEmbedding φ) (α κ ε : G →* Eˣ) (b : G → E)
    (hb : ∀ g h, b (g * h) = α g * b h + b g * κ h)
    (hα : Continuous fun g => (α g : E)) (hκ : Continuous fun g => (κ g : E)) (hbc : Continuous b)
    (H : Subgroup G) [H.Normal] (hH : IsOpen (H : Set G)) (hcr : CrOn φ (two α κ b hb) H)
    (hε : ∀ g, (α g : E) = ε g * κ g) :
    (fun g => b g * (((κ g)⁻¹ : Eˣ) : E)) ∈ UpperTheory.V.Loc.finiteCocycles φ (chRep ε) := by
  have c2 := cont_two α κ b hb hα hκ hbc
  have cα : ReciprocityTheory.Gal.ContAction (chRep α) := (hα.comp continuous_fst).mul continuous_snd
  have cκ : ReciprocityTheory.Gal.ContAction (chRep κ) := (hκ.comp continuous_fst).mul continuous_snd
  have e1 : ∀ g x, LinearMap.inl E E E (chRep α g x) = two α κ b hb g (LinearMap.inl E E E x) := by
    intro g x
    simp [two_apply, chRep]
  have e2 : ∀ g x, LinearMap.snd E E E (two α κ b hb g x) = chRep κ g (LinearMap.snd E E E x) := by
    intro g x
    simp [two_apply, chRep]
  have h1 := (crOn_map φ hφ _ _ cα c2 _ e1 H hH).1 LinearMap.inl_injective hcr
  have h2 := (crOn_map φ hφ _ _ c2 cκ _ e2 H hH).2 LinearMap.snd_surjective hcr
  have key := (crExt φ hφ (chRep α) (two α κ b hb) cα c2 κ (LinearMap.inl E E E) (LinearMap.snd E E E) (0, 1)
    (fun g => b g * (((κ g)⁻¹ : Eˣ) : E)) LinearMap.inl_injective Function.Exact.inl_snd rfl e1
    (fun g => by
      ext <;> simp [two_apply]
      field_simp) H hH h1 h2).1 hcr
  have e3 : twist κ⁻¹ (chRep α) = chRep ε := by
    refine MonoidHom.ext fun g => LinearMap.ext fun x => ?_
    change (((κ g)⁻¹ : Eˣ) : E) * ((α g : E) * x) = (ε g : E) * x
    rw [hε, mul_comm (ε g : E), mul_assoc, Units.inv_mul_cancel_left]
  rwa [e3] at key

end Cr

end UpperTheory.V.Z.J.StepF

open UpperTheory.V.Z.J.StepF in
theorem UpperTheory.V.Z.J.stepF :
    ∀ {l : ℕ} [Fact l.Prime] {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (φ : G →* GQ l), IsOpenEmbedding φ → ∀ {E : Type} [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] [Algebra ℤ_[l] E] [IsScalarTower ℤ_[l] ℚ_[l] E] [TopologicalSpace E] [IsModuleTopology ℚ_[l] E] [IsTopologicalRing E] (t : G →* GL (Fin 3) E), Continuous (fun g => (t g : Matrix (Fin 3) (Fin 3) E)) → (∀ g i j, j < i → (t g : Matrix (Fin 3) (Fin 3) E) i j = 0) → ∀ (H : Subgroup G) [H.Normal], IsOpen (H : Set G) → CrOn φ (colRep t) H → ∀ i : Fin 2, (∀ g, (t g : Matrix (Fin 3) (Fin 3) E) i.castSucc i.castSucc = (cycA l l E (φ g) : E) * (t g : Matrix (Fin 3) (Fin 3) E) i.succ i.succ) → (fun g => (t g : Matrix (Fin 3) (Fin 3) E) i.castSucc i.succ * ((t g)⁻¹ : GL (Fin 3) E) i.succ i.succ) ∈ UpperTheory.V.Loc.finiteCocycles φ (chRep ((cycA l l E).comp φ)) := by
  intro l _ G _ _ _ φ hφ E _ _ _ _ _ _ _ _ t htc ht H _ hH hcr i hi
  have h10 := fun g => ht g 1 0 (by decide)
  have h20 := fun g => ht g 2 0 (by decide)
  have h21 := fun g => ht g 2 1 (by decide)
  have ce : ∀ a b, Continuous fun g => (t g : Matrix (Fin 3) (Fin 3) E) a b :=
    fun a b => htc.matrix_elem a b
  have cc : ReciprocityTheory.Gal.ContAction (colRep t) :=
    (htc.comp continuous_fst).matrix_mulVec continuous_snd
  have hd : ∀ j g, ((diag t ht j g : Eˣ) : E) = (t g : Matrix (Fin 3) (Fin 3) E) j j := fun j g => rfl
  have hb : ∀ g h, (t (g * h) : Matrix (Fin 3) (Fin 3) E) i.castSucc i.succ =
      (diag t ht i.castSucc g : E) * (t h : Matrix (Fin 3) (Fin 3) E) i.castSucc i.succ +
      (t g : Matrix (Fin 3) (Fin 3) E) i.castSucc i.succ * (diag t ht i.succ h : E) := by
    intro g h
    rw [mul_entry, hd, hd]
    fin_cases i <;> simp [h10, h20, h21]
  have c2 := cont_two _ _ _ hb (ce _ _) (ce _ _) (ce _ _)
  have h2 : CrOn φ (two (diag t ht i.castSucc) (diag t ht i.succ)
      (fun g => (t g : Matrix (Fin 3) (Fin 3) E) i.castSucc i.succ) hb) H := by
    fin_cases i
    · refine (crOn_map φ hφ _ _ c2 cc
        (LinearMap.coprod (LinearMap.single E (fun _ : Fin 3 => E) 0) (LinearMap.single E (fun _ : Fin 3 => E) 1))
        (fun g x => ?_) H hH).1 (fun x y h => ?_) hcr
      · funext k
        fin_cases k <;> simp [two_apply, hd, colRep, Matrix.mulVec, dotProduct, Fin.sum_univ_three, h10, h20, h21]
      · exact Prod.ext (by simpa using congrFun h 0) (by simpa using congrFun h 1)
    · refine (crOn_map φ hφ _ _ cc c2
        (LinearMap.prod (LinearMap.proj (R := E) (φ := fun _ : Fin 3 => E) 1) (LinearMap.proj 2))
        (fun g x => ?_) H hH).2 (fun y => ⟨![0, y.1, y.2], rfl⟩) hcr
      ext <;> simp [two_apply, hd, colRep, Matrix.mulVec, dotProduct, Fin.sum_univ_three, h10, h20, h21]
  have key := core φ hφ _ _ ((cycA l l E).comp φ) _ hb (ce _ _) (ce _ _) (ce _ _) H hH h2 hi
  convert key using 3 with g
  rw [← map_inv, ← map_inv, hd]
