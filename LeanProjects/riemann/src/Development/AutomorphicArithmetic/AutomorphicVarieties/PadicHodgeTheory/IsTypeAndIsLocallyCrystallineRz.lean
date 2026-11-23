import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.IsInertiaInfiniteCyclotomic
import Development.AutomorphicArithmetic.AutomorphicVarieties.PublishedTheorems.KisinCrTrivial
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.MemFilDDiag
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.CharFil
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.IsCrysOfInertia
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.AdmProd
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.AdmSub
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.OpenField
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.IsCrIff
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.PtCont
open Formalism.BasicNotions Formalism.BasicNotions.Loc ReciprocityTheory.Gal Module UpperTheory.V.Loc UpperTheory.V.U3 UpperTheory.V.Alg UpperTheory.V.Published IsLocalRing Polynomial

namespace UpperTheory.V.Loc.R0

open Topology TensorProduct

variable {l : ℕ} [Fact l.Prime] {E : Type} [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  [Algebra ℤ_[l] E] [IsScalarTower ℤ_[l] ℚ_[l] E] [TopologicalSpace E] [IsModuleTopology ℚ_[l] E]
  [IsTopologicalRing E]

private theorem cont_ch {G : Type} [Group G] [TopologicalSpace G] {κ : G →* Eˣ} (h : Continuous κ) :
    ContAction (chRep κ) :=
  (Units.continuous_val.comp (h.comp continuous_fst)).mul continuous_snd

private theorem cont_prod {G V V' : Type} [Group G] [TopologicalSpace G] [AddCommGroup V] [Module E V]
    [TopologicalSpace V] [AddCommGroup V'] [Module E V'] [TopologicalSpace V'] {ρ : Representation E G V}
    {ρ' : Representation E G V'} (h : ContAction ρ) (h' : ContAction ρ') : ContAction (ρ.prod ρ') :=
  (h.comp (continuous_fst.prodMk continuous_snd.fst)).prodMk (h'.comp (continuous_fst.prodMk continuous_snd.snd))

private theorem isCr_char (H : Subgroup (GQ l)) (hH : IsOpen (H : Set (GQ l))) (κ : GQ l →* Eˣ) (hκ : Continuous κ)
    (w : ℤ) (hw : ∀ g ∈ H, g ∈ Iq l → κ g = cycA l l E g ^ w) : IsCr H.subtype (chRep (κ.comp H.subtype)) :=
  crUnr H.subtype hH.isOpenEmbedding_subtypeVal _ (cont_ch (hκ.comp continuous_subtype_val)) w fun g hg x => by
    rw [Subgroup.subtype_apply, ← hw g g.2 hg]
    rfl

private theorem isCr_diag (H : Subgroup (GQ l)) (hH : IsOpen (H : Set (GQ l))) (κ : Fin 3 → GQ l →* Eˣ)
    (hκ : ∀ a, Continuous (κ a)) (w : Fin 3 → ℤ) (hw : ∀ a, ∀ g ∈ H, g ∈ Iq l → κ a g = cycA l l E g ^ w a)
    (ρ : ↥H →* GL (Fin 3) E)
    (hρ : ∀ g, (ρ g : Matrix (Fin 3) (Fin 3) E) = Matrix.diagonal fun a => (κ a g : E)) :
    IsCr H.subtype (colRep ρ) := by
  have hφ : IsOpenEmbedding H.subtype := hH.isOpenEmbedding_subtypeVal
  have hc : ∀ a, ContAction (chRep ((κ a).comp H.subtype)) := fun a =>
    cont_ch ((hκ a).comp continuous_subtype_val)
  have hcr := fun a => isCr_char H hH (κ a) (hκ a) (w a) (hw a)
  have hp := fun a g x => proj_diag (κ := fun a => (κ a).comp H.subtype) hρ a g x
  have h0 : ContAction (colRep ρ) := continuous_pi fun a => by
    have := (hc a).comp (continuous_fst.prodMk ((continuous_apply a).comp continuous_snd) :
      Continuous fun p : ↥H × (Fin 3 → E) => (p.1, p.2 a))
    exact this.congr fun p => (hp a p.1 p.2).symm
  have h1 := (isCrys_isDR_prod _ hφ _ _ (hc 0) (cont_prod (hc 1) (hc 2))).1 (hcr 0)
    ((isCrys_isDR_prod _ hφ _ _ (hc 1) (hc 2)).1 (hcr 1) (hcr 2))
  refine ((isCrys_isDR_sub_quot _ hφ _ _ h0 (cont_prod (hc 0) (cont_prod (hc 1) (hc 2)))
    ((LinearMap.proj 0).prod ((LinearMap.proj 1).prod (LinearMap.proj 2))) fun g x => ?_).1 fun x y h => ?_).1 h1
  · exact Prod.ext (hp 0 g x) (Prod.ext (hp 1 g x) (hp 2 g x))
  · funext a
    fin_cases a
    · exact congrArg Prod.fst h
    · exact congrArg (fun z => z.2.1) h
    · exact congrArg (fun z => z.2.2) h

private theorem open_GK (K : FinExt l) : IsOpen (GK K : Set (GQ l)) :=
  haveI := K.2
  IntermediateField.fixingSubgroup_isOpen K.1

private theorem fil_char (K : FinExt l) (H : Subgroup (GQ l)) (hH : IsOpen (H : Set (GQ l))) (κ : GQ l →* Eˣ)
    (hκ : Continuous κ) (w : ℤ) (hw : ∀ g ∈ H, g ∈ Iq l → κ g = cycA l l E g ^ w) :
    IsDr (GK K).subtype (chRep (κ.comp (GK K).subtype)) ∧ ∀ i : ℤ,
      (i ≤ -w → FilD (GK K).subtype (chRep (κ.comp (GK K).subtype)) i =
        Ddr (GK K).subtype (chRep (κ.comp (GK K).subtype))) ∧
      (-w < i → FilD (GK K).subtype (chRep (κ.comp (GK K).subtype)) i = ⊥) :=
  charFil (GK K).subtype (open_GK K).isOpenEmbedding_subtypeVal _
    (Units.continuous_val.comp (hκ.comp continuous_subtype_val)) w
    ⟨H.comap (GK K).subtype, hH.preimage continuous_subtype_val, fun g hg hI => hw g hg hI⟩

private theorem cr_char {K L : FinExt l} (h : K.1 ≤ L.1) (κ τ : GQ l →* Eˣ) (hκ : Continuous κ) (hτ : Continuous τ)
    (w : ℤ) (hw : ∀ g ∈ Iq l, κ g = cycA l l E g ^ w * τ g) (hL : ∀ g ∈ GK L, τ g = 1) :
    ∃ x ∈ Dcr (GK L).subtype (chRep ((κ.comp (GK K).subtype).comp (incl h))),
      (∀ y ∈ Dcr (GK L).subtype (chRep ((κ.comp (GK K).subtype).comp (incl h))),
        ∃! c : E ⊗[ℚ_[l]] ↥(K0 L), y = smulC E L c x) ∧
      ∀ γ, actC (GK K).subtype (chRep (κ.comp (GK K).subtype)) γ x = (τ γ : E) • x := by
  obtain ⟨x, hx, hb⟩ := char_cr (κ / τ) (isCr_char _ (open_GK _) _ (hκ.div' hτ) w fun g _ hg => by
    rw [MonoidHom.div_apply, hw g hg, mul_div_cancel_right])
  have e : (κ.comp (GK K).subtype).comp (incl h) = (κ / τ).comp (GK L).subtype := by
    ext1 g
    change κ g = κ g / τ g
    rw [hL g g.2, div_one]
  rw [e]
  refine ⟨x, (mem_Dcr _ _ _).2 fun g => hx g, hb L, fun γ => ?_⟩
  conv_rhs => rw [← hx γ]
  generalize x = y
  induction y using TensorProduct.induction_on with
  | zero => simp only [map_zero, smul_zero]
  | tmul v b =>
    change ((κ γ : E) • v) ⊗ₜ _ = ((τ γ : E) • (((κ γ / τ γ : Eˣ) : E) • v)) ⊗ₜ _
    rw [smul_smul, ← Units.val_mul, mul_div_cancel]
    rfl
  | add a b ha hb => simp only [map_add, ha, hb, smul_add]

end UpperTheory.V.Loc.R0

theorem UpperTheory.V.Loc.isType_and_isLocallyCrystalline_rz :
    ∀ {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CharZero O] [Algebra ℤ_[l] O] [Module.Finite ℤ_[l] O] [IsAdicComplete (maximalIdeal O) O] (D : Dat3 l O) (E : Type) [Field E] [Algebra ℚ_[l] E] [Module.Finite ℚ_[l] E] [Algebra O E] [Algebra ℤ_[l] E] [IsScalarTower ℤ_[l] O E] [IsScalarTower ℤ_[l] ℚ_[l] E], D.IsType (D.rz E) ∧ D.IsLCr (D.rz E) := by
  intro l _ O _ _ _ _ _ _ _ D E _ _ _ _ _ _ _
  letI : TopologicalSpace E := moduleTopology ℚ_[l] E
  haveI : IsModuleTopology ℚ_[l] E := ⟨rfl⟩
  haveI : IsTopologicalRing E := IsModuleTopology.isTopologicalRing ℚ_[l] E
  let j : Oˣ →* Eˣ := Units.map (algebraMap O E : O →* E)
  let κ : Fin 3 → GQ l →* Eˣ := fun a => (zpowGroupHom (wt1 a)).comp (j.comp D.Ψ)
  let τ : Fin 3 → GQ l →* Eˣ := fun a => (zpowGroupHom (wt1 a)).comp (j.comp D.τ)
  let w : Fin 3 → ℤ := fun a => D.e * wt1 a
  have hΨ : Continuous fun g => ((j (D.Ψ g) : Eˣ) : E) :=
    (ptCont (l := l) O E (Algebra.ofId O E)).1 _ _ D.Ψ_cont
  have hΨ' : Continuous (j.comp D.Ψ) := Units.continuous_iff.2 ⟨hΨ, (hΨ.comp continuous_inv).congr fun g => by
    simp only [Function.comp_apply, map_inv, MonoidHom.comp_apply]⟩
  have hτ' : Continuous (j.comp D.τ) := continuous_of_continuousAt_one _
    (continuousAt_const.congr (Filter.eventually_of_mem (D.τ_open.mem_nhds D.τ.ker.one_mem) fun g hg => by
      change 1 = j (D.τ g)
      rw [show D.τ g = 1 from hg, map_one]))
  have hκ : ∀ a, Continuous (κ a) := fun a => hΨ'.zpow _
  have hτ : ∀ a, Continuous (τ a) := fun a => hτ'.zpow _
  have hw : ∀ a, ∀ g ∈ Iq l, κ a g = cycA l l E g ^ w a * τ a g := by
    intro a g hg
    have h1 : j (cycA l l O g) = cycA l l E g := Units.ext (IsScalarTower.algebraMap_apply ℤ_[l] O E _).symm
    change j (D.Ψ g) ^ wt1 a = _ * j (D.τ g) ^ wt1 a
    rw [D.Ψ_I g hg, map_mul, map_pow, h1, mul_zpow, ← zpow_natCast, ← zpow_mul]
  have hτ1 : ∀ a, ∀ g ∈ D.HL, τ a g = 1 := fun a g hg => by
    change j (D.τ g) ^ wt1 a = 1
    rw [show D.τ g = 1 from hg.2, map_one, one_zpow]
  have hw' : ∀ a, ∀ g ∈ D.HL, g ∈ Iq l → κ a g = cycA l l E g ^ w a := fun a g hg hI => by
    rw [hw a g hI, hτ1 a g hg, mul_one]
  have hker : D.η.ker = GK D.Kv := Subgroup.ext D.η_ker
  have hH : IsOpen (D.HL : Set (GQ l)) := by
    have := (R0.open_GK D.Kv).inter D.τ_open
    rwa [← hker] at this
  let σ : GQ l →* GL (Fin 3) E := (tor E).comp (j.comp D.Ψ)
  have hσ : ∀ g, σ g = (D.rz E g).left := fun g => Units.ext (by
    change Matrix.diagonal _ = (Matrix.diagonal _).map (algebraMap O E)
    rw [Matrix.diagonal_map (map_zero _)]
    congr 1
    funext a
    exact congrArg Units.val (map_zpow j _ _).symm)
  refine ⟨⟨σ.comp (GK D.Kv).subtype, fun g => hσ g, ?_, ?_⟩, σ.comp D.HL.subtype, fun g => hσ g,
    R0.isCr_diag _ hH κ hκ w hw' _ fun _ => rfl⟩
  · have he := D.e_pos
    refine R0.hodge_diag (κ := fun a => (κ a).comp (GK D.Kv).subtype) (fun _ => rfl) (fun a => -w a) ?_ _ ?_ ?_
      (fun a => (R0.fil_char D.Kv _ hH _ (hκ a) _ (hw' a)).2) fun a => ?_
    · intro a b hab
      fin_cases a <;> fin_cases b <;> simp [w, wt1] at hab ⊢ <;> omega
    · intro a
      fin_cases a <;> simp [w, wt1, hodge0]
    · intro i hi
      have h0 := hi 0
      have h1 := hi 1
      have h2 := hi 2
      simp [w, wt1] at h0 h1 h2
      rw [hodge0, if_neg (by omega)]
    · obtain ⟨x, hx, hb⟩ := R0.char_dr (κ a) (R0.fil_char _ _ hH _ (hκ a) _ (hw' a)).1
      exact ⟨x, (R0.mem_Ddr _ _ _).2 fun g => hx g, hb D.Kv⟩
  · obtain ⟨L, -, -, -, -, hL, -, -⟩ := openField D.HL.subtype hH.isOpenEmbedding_subtypeVal
    rw [Subgroup.range_subtype] at hL
    have hle : GK L ≤ GK D.Kv := by
      rw [← hL, ← hker]
      exact inf_le_left
    have h : D.Kv.1 ≤ L.1 := by
      have : IsGalois ℚ_[l] (Om l) := inferInstance
      rw [← InfiniteGalois.fixedField_fixingSubgroup D.Kv.1, ← InfiniteGalois.fixedField_fixingSubgroup L.1]
      exact IntermediateField.fixedField_le hle
    choose x hx hb ht using fun a => R0.cr_char h (κ a) (τ a) (hκ a) (hτ a) (w a) (hw a) (hL ▸ hτ1 a)
    have hN : (GK L).Normal := by
      rw [← hL, Dat3.HL]
      infer_instance
    have hC := (isCrIff L _).1.1 (R0.isCr_diag (GK L) (R0.open_GK L) κ hκ w (hL ▸ hw') (σ.comp (GK L).subtype)
      fun _ => rfl)
    have key := R0.crys_diag (ρ := σ.comp (GK D.Kv).subtype) (κ := fun a => (κ a).comp (GK D.Kv).subtype)
      (fun _ => rfl) h inferInstance hC (fun a γ => (τ a γ : E)) x hx hb ht
    refine ⟨L, h, ?_⟩
    convert key using 2 with γ
    simp [Fin.sum_univ_three, τ, j, wt1]
