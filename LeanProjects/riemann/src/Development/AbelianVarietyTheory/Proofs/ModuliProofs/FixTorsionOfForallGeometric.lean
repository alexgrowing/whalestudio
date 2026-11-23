import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ObjMapUniqueOfIsDominant
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.EqCompSectionOfSurjectiveAppTop
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.CompAutEqOfSerreBaseChange

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

namespace GlobalTheory

theorem eq_id_of_forall_geometric_fibre (hG : Out.GlobalFnsSt) {S : Scheme.{0}} (A : Over S)
    [GrpObj A] (hA : IsAbelianScheme A) (σ : A ⟶ A) (h0 : η[A] ≫ σ = η[A])
    (hσ : ∀ t : S, ∃ (S' X : Scheme.{0}) (f : S' ⟶ S) (g : X ⟶ A.left) (q : X ⟶ S') (y : S'),
      f y = t ∧ IsPullback g q A.hom f ∧ g ≫ σ.left = g) : σ = 𝟙 A := by
  have := hA.proper
  let u : A ⟶ A := σ * (𝟙 A)⁻¹
  have hu : ∀ {T : Over S} (x : T ⟶ A), x ≫ σ = x → x ≫ u = 1 := fun x hx => by
    simp only [u, MonObj.comp_mul, GrpObj.comp_inv, hx, Category.comp_id, mul_inv_cancel]
  have hη : (η[A] : 𝟙_ (Over S) ⟶ A).left ≫ A.hom = 𝟙 S := Over.w η[A]
  have hfib : ∀ (t : S) (x : A.left), A.hom x = t →
      u.left x = (η[A] : 𝟙_ (Over S) ⟶ A).left t := by
    intro t x hx
    obtain ⟨S', X, f, g, q, y, hy, hg, e⟩ := hσ t
    obtain ⟨z, rfl, -⟩ := Scheme.exists_preimage_of_isPullback hg x y (hx.trans hy.symm)
    let x₀ : Over.mk (g ≫ A.hom) ⟶ A := Over.homMk g rfl
    have h₀ : g ≫ u.left = (g ≫ A.hom) ≫ (η[A] : 𝟙_ (Over S) ⟶ A).left :=
      congrArg (fun q => q.left) (hu x₀ (Over.OverMorphism.ext e))
    rw [← Scheme.Hom.comp_apply, h₀, Scheme.Hom.comp_apply, Scheme.Hom.comp_apply, hx]
  have key : u.left = A.hom ≫ (η[A] : 𝟙_ (Over S) ⟶ A).left ≫ u.left := by
    refine Scheme.hom_ext_of_forall _ _ fun x => ?_
    obtain ⟨V, hV, e⟩ := local_rigidity _ _ _ A.hom _ u.left hη inferInstance
      (surjective_app_of_isAbelianScheme hG A hA) (A.hom x) _ (hfib _)
    exact ⟨A.hom ⁻¹ᵁ V, hV, e⟩
  have h₁ : u = toUnit A ≫ η[A] ≫ u := Over.OverMorphism.ext key
  rw [hu η[A] h0, MonObj.comp_one] at h₁
  exact mul_inv_eq_one.1 h₁

theorem serre_any_base (hL : Out.Laws) {S : Scheme.{0}} (P : Out.PolAV S) (M : ℕ) (hM : 3 ≤ M)
    (σ : P.A ≅ P.A) (hσ : IsMonHom σ.hom)
    (hloc : ∀ p : S, ∃ V : S.Opens, p ∈ V ∧
      ∃ c : LB.Gen ((LB.LinComb P.L (K := Fin 2) ![σ.hom.left, 𝟙 P.A.left] ![1, -1]).pull
        (P.A.hom ⁻¹ᵁ V).ι), c.IsGen)
    (hfix : ∀ (T : Over S) (x : T ⟶ P.A), x ^ M = 1 → x ≫ σ.hom = x) : σ.hom = 𝟙 P.A := by
  refine eq_id_of_forall_geometric_fibre hL.globalFns P.A P.isAb σ.hom (IsMonHom.one_hom σ.hom)
    fun t => ?_
  obtain ⟨V, hV, c, hc⟩ := hloc t
  have hf : ∀ y, S.fromSpecResidueField t y = t := Scheme.fromSpecResidueField_apply t
  obtain ⟨X, g, q, hg, e⟩ := comp_aut_eq_of_serre_baseChange hL.polBaseChange
    (S.fromSpecResidueField t) P M
    (fun P' σ' h' ⟨c', hc'⟩ hx => hL.serre _ P' M hM σ' h' (fun _ => ⟨⊤, trivial,
      gen_chartPull (chartPullPull _ _ _ rfl) c' hc'⟩) hx)
    σ hσ V (fun y => by rw [hf]; exact hV) c hc hfix
  exact ⟨_, X, _, g, q, (default : PrimeSpectrum (S.residueField t)), hf _, hg, e⟩

theorem fix_torsion_of_forall_geometric {S : Scheme.{0}} (A : Over S) [GrpObj A] (n : ℕ)
    [Etale (Out.mulA A n).left] (σ : A ⟶ A) [IsMonHom σ]
    (h : ∀ (k : Type) [Field k] [IsAlgClosed k] (t : Sp k ⟶ S) (x : Over.mk t ⟶ A),
      x ^ n = 1 → x ≫ σ = x) (T : Over S) (x : T ⟶ A) (hx : x ^ n = 1) : x ≫ σ = x := by
  have e : ∀ y : T ⟶ A, y ≫ Out.mulA A n = y ^ n := fun y => by
    rw [Out.mulA, MonObj.comp_pow, Category.comp_id]
  have hx' : (x ≫ σ) ^ n = 1 := by
    rw [← MonObj.pow_comp, hx, MonObj.one_comp]
  apply Over.OverMorphism.ext
  refine eq_of_range_equalizer_ι_eq_univ (Out.mulA A n).left
    (by rw [← Over.comp_left, ← Over.comp_left, e, e, hx, hx']) (Set.eq_univ_of_forall fun z => ?_)
  let K : Type := AlgebraicClosure (T.left.residueField z)
  let j : Sp K ⟶ T.left :=
    Spec.map (CommRingCat.ofHom (algebraMap (T.left.residueField z) K)) ≫
      T.left.fromSpecResidueField z
  have hj : ∀ p, j p = z := fun p =>
    (Scheme.Hom.comp_apply _ _ p).trans (Scheme.fromSpecResidueField_apply z _)
  let j' : Over.mk (j ≫ T.hom) ⟶ T := Over.homMk j rfl
  have h₁ := h K (j ≫ T.hom) (j' ≫ x) (by rw [← MonObj.comp_pow, hx, MonObj.comp_one])
  replace h₁ := (Category.assoc _ _ _).symm.trans h₁
  exact range_subset_range_equalizer_ι j (congrArg (fun q => q.left) h₁)
    ⟨(default : PrimeSpectrum K), hj _⟩

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}

theorem obj_aut_fix_geometric_torsion {B : Type} [CommRing B] {b : Base l B} {S : Scheme.{0}}
    {s : S ⟶ Sp B} (o : Obj D l b s) (θ : o.t.G ≅ o.t.G) [IsMonHom θ.hom]
    (hact : ∀ a, o.t.act.act a ≫ θ.hom = θ.hom ≫ o.t.act.act a)
    (hL : LBIso o.t.PP.L (o.t.PP.L.pull θ.hom.left)) (heta : ∀ a, o.eta a ≫ θ.hom = o.eta a)
    (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ S) (y : Over.mk x ⟶ o.t.G)
    (hy : y ^ l.M = 1) : y ≫ θ.hom = y := by
  obtain ⟨w, hw⟩ := hL
  obtain ⟨-, I, -, -, hI⟩ := o.geom k x (Spec.preimage (x ≫ s)).hom (Spec.map_preimage _).symm
  refine ObjRigid.fix_torsion l I (IsMonHom.monoidHom θ.hom (Over.mk x)) (fun a z => ?_)
    (fun z z' c c' h h' => ?_) (fun a ha => ?_) y hy
  · show (z ≫ _) ≫ θ.hom = (z ≫ θ.hom) ≫ _
    rw [Category.assoc, hact, Category.assoc]
  · have : Subsingleton (Over.mk x).left := inferInstanceAs (Subsingleton (Sp k))
    exact H1.unitOn_injective
      (ObjRigid.weil_eq_of_iso (T := Over.mk x) o.t.PP.isLB θ w hw _ z z' _ _ h h')
  · show _ ≫ θ.hom = _
    rw [← hI a ha, Category.assoc, heta]

theorem obj_rigid_of_pol : Out.Laws → (∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (B : Type) [CommRing B] (b : Base l B) (S : Scheme.{0}) (s : S ⟶ Sp B) (o : Obj D l b s), IsAbelianScheme o.t.G ∧ SmoothOfRelativeDimension (Module.finrank ℚ E / 2 * (D.p + D.q)) o.t.G.hom ∧ Out.Rigidified o.t.G o.t.PP.L ∧ Out.Sym o.t.G o.t.PP.L) → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (B B' : Type) [CommRing B] [CommRing B'] (b : Base l B) (b' : Base l B') (S S' : Scheme.{0}) (s : S ⟶ Sp B) (s' : S' ⟶ Sp B') (o : Obj D l b s) (o' : Obj D l b' s') (f : S' ⟶ S), ∀ m m' : SABMap o'.t o.t f, (∀ a, ∃ σ, (o'.eta a).left ≫ m.φ = σ ∧ (o'.eta a).left ≫ m'.φ = σ) → m.φ = m'.φ := by
  intro hL hpol E _ _ _ H D l B B' _ _ b b' S S' s s' o o' f m m' heta
  obtain ⟨hA, hd, hr, hs⟩ := hpol E H D l B' b' S' s' o'
  obtain ⟨θ, hθ, hφ, hact, -, w, hw, -⟩ := sabMap_iso m m' rfl rfl
  have hη : ∀ a, o'.eta a ≫ θ.hom = o'.eta a := fun a => by
    obtain ⟨σ, h₁, h₂⟩ := heta a
    apply Over.OverMorphism.ext
    apply m'.cart.1.hom_ext
    · rw [Over.comp_left, Category.assoc]
      exact (congrArg _ hφ).trans (h₁.trans h₂.symm)
    · rw [Over.w, Over.w]
  let P : Out.PolAV S' :=
    { A := o'.t.G, g := _, smoothDim := hd, L := o'.t.PP.L, isLB := o'.t.PP.isLB,
      ample := o'.ample, ktriv := o'.ktriv, isAb := hA, rigid := hr, sym := hs }
  have hM : 0 < l.M := lt_of_lt_of_le (by norm_num) l.three_le
  have hMu : IsUnit (l.M : Γ(S', ⊤)) := by
    simpa using (b'.unit _ hM).map ((Scheme.ΓSpecIso (CommRingCat.of B')).inv ≫ s'.appTop).hom
  have := hA.smooth
  have : Etale (Out.mulA o'.t.G l.M).left := GrpTangent.etale_id_pow o'.t.G hMu
  have h : θ.hom = 𝟙 _ := by
    refine serre_any_base hL P l.M l.three_le θ hθ (fun _ => ⟨⊤, trivial, ?_⟩)
      (fix_torsion_of_forall_geometric o'.t.G l.M θ.hom
        (obj_aut_fix_geometric_torsion o' θ hact ⟨w, hw⟩ hη))
    obtain ⟨t, ht⟩ := gen_of_iso ((isGen_iff w).1 hw) (o'.t.G.hom ⁻¹ᵁ ⊤).ι
    refine gen_chartPull (chartPullOut o'.t.PP.L _ _ _ _ fun n => ?_) t ht
    fin_cases n
    exacts [rfl, (Category.comp_id _).symm]
  rw [← hφ, h, Over.id_left, Category.id_comp]

end GlobalTheory
