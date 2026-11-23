import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeDeformations.HostNumber
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.LocalPublishedTheorems
import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeDeformations.RigFin
import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeDeformations.RigDesc
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.Z1fCoef

open NumberField Matrix IsLocalRing Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.GalOfCusp UpperTheory.V.HV UpperTheory.V.U3 UpperTheory.V.Alg UpperTheory.V.Aut UpperTheory.V.UnitaryThreeInertia

private theorem rigloc_adFun {m : ℕ} {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) (x : GG m R)
    (X : Matrix (Fin m) (Fin m) R) : (x.adFun X).map f = (GG.map f x).adFun (X.map f) := by
  have h1 : (((GG.map f x).left⁻¹ : GL (Fin m) S) : Matrix (Fin m) (Fin m) S) =
      ((x.left⁻¹ : GL (Fin m) R) : Matrix (Fin m) (Fin m) R).map f := rfl
  unfold GG.adFun
  rw [h1, GG.map_mat, GG.map_right, Matrix.map_mul, Matrix.map_mul]
  congr 2
  split_ifs
  · rfl
  · unfold thetaLie
    rw [Matrix.map_neg _ (map_neg f), Matrix.map_mul, Matrix.map_mul, Jmat_map, Matrix.transpose_map]

private theorem rigloc_conj {m : ℕ} {G R S : Type} [Group G] [CommRing R] [CommRing S] (f : R →+* S)
    (h : GL (Fin m) R) (r : G →* GG m R) (g : G) :
    GG.map f (conjBy h r g) = conjBy (Matrix.GeneralLinearGroup.map f h) ((GG.map f).comp r) g := by
  have h1 : GG.map f (GG.ofGL h) = GG.ofGL (Matrix.GeneralLinearGroup.map f h) := rfl
  simp only [conjBy, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, map_mul, map_inv, h1]

private theorem rigloc_mul {m : ℕ} {R : Type} [CommRing R] (y a : Matrix (Fin m) (Fin m) R) (i j : Fin m) :
    (((1 + y.map (TrivSqZeroExt.inr : R → DualNumber R)) * a.map (algebraMap R (DualNumber R))) i j).fst = a i j ∧
    (((1 + y.map (TrivSqZeroExt.inr : R → DualNumber R)) * a.map (algebraMap R (DualNumber R))) i j).snd =
      (y * a) i j := by
  rw [Matrix.add_mul, Matrix.one_mul, Matrix.add_apply, Matrix.mul_apply, Matrix.mul_apply]
  simp [TrivSqZeroExt.fst_sum, TrivSqZeroExt.snd_sum, TrivSqZeroExt.algebraMap_eq_inl]

set_option maxHeartbeats 800000 in
theorem UpperTheory.V.UnitaryThreeInertia.rig_loc :
    UpperTheory.V.Loc.LocalPublishedTheorems → ∀ {l : ℕ} [Fact l.Prime] {Γ : Type} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] (φ : Γ →* Formalism.BasicNotions.Loc.GQ l), Topology.IsOpenEmbedding φ → ∀ (η : Γ →* ℤˣ), IsLocallyConstant η → ∀ (r : Γ →* GG 3 (PadicAlgCl l)) (y : Γ → Matrix (Fin 3) (Fin 3) (PadicAlgCl l)) (r' : Γ →* GG 3 (DualNumber (PadicAlgCl l))) (h : GL (Fin 3) (DualNumber (PadicAlgCl l))), HasMult η r → Continuous (mats r) → Continuous y → IsCoc r y → IsDeform ((GG.map (algebraMap (PadicAlgCl l) (DualNumber (PadicAlgCl l)))).comp r) (fun g => (y g).map (TrivSqZeroExt.inr : (PadicAlgCl l) → DualNumber (PadicAlgCl l))) r' → ∀ (H : Subgroup Γ) [H.Normal], IsOpen (H : Set Γ) → H ≤ η.ker → Upper η (conjBy h⁻¹ r') → ∀ w : Fin 3 → ℤ, StrictAnti w → (∀ g ∈ H, φ g ∈ UpperTheory.V.Loc.Iq l → ∀ a, (conjBy h⁻¹ r' g).mat a a = ((UpperTheory.V.Loc.cycA l l (DualNumber (PadicAlgCl l)) (φ g) ^ w a : (DualNumber (PadicAlgCl l))ˣ) : DualNumber (PadicAlgCl l))) → (∀ i j : Fin 3, i < j → ∃ g ∈ H, ((conjBy h⁻¹ r' g).mat i i).fst ≠ ((conjBy h⁻¹ r' g).mat j j).fst * ((UpperTheory.V.Loc.cycA l l (PadicAlgCl l) (φ g) : (PadicAlgCl l)ˣ) : (PadicAlgCl l))) → y ∈ UpperTheory.V.Loc.finiteCocycles φ (adRep r) := by
  intro P l _ Γ _ _ _ φ hφ η hη r y r' h hm hr hy hcoc hdef H _ hH hHη hU w hw hκ hne
  have hc : IsClosed (φ.range : Set (Formalism.BasicNotions.Loc.GQ l)) := φ.range.isClosed_of_isOpen hφ.isOpen_range
  haveI : CompactSpace Γ := (Topology.IsClosedEmbedding.mk hφ.isEmbedding hc).compactSpace
  haveI : T2Space Γ := hφ.isEmbedding.t2Space
  have hfst : ∀ g a b, ((r' g).mat a b).fst = (r g).mat a b := fun g a b => by
    rw [(hdef g).2]; exact (rigloc_mul (y g) (r g).mat a b).1
  have hsnd : ∀ g a b, ((r' g).mat a b).snd = (y g * (r g).mat) a b := fun g a b => by
    rw [(hdef g).2]; exact (rigloc_mul (y g) (r g).mat a b).2
  obtain ⟨L, f, s', h₁, hf, hs', hh⟩ := rig_desc r' h
    (fun a b => by simp only [hfst]; exact hr.matrix_elem a b)
    (fun a b => by simp only [hsnd]; exact (hy.matrix_mul hr).matrix_elem a b)
  haveI := L.2
  haveI : IsModuleTopology ℚ_[l] ↥L.1 := isModuleTopologyOfFiniteDimensional
  let ι : ↥L.1 →+* PadicAlgCl l := L.1.val.toRingHom
  have hι : Function.Injective ι := Subtype.val_injective
  have hιm : Function.Injective fun X : Matrix (Fin 3) (Fin 3) ↥L.1 => X.map ι := Matrix.map_injective hι
  have hfi : Function.Injective f := fun a b hab => by
    ext
    · rw [← (hf a).1, ← (hf b).1, hab]
    · rw [← (hf a).2, ← (hf b).2, hab]
  have hcont : ∀ z : Γ → Matrix (Fin 3) (Fin 3) ↥L.1, Continuous (fun g => (z g).map ι) → Continuous z :=
    fun z hz => continuous_matrix fun a b => Topology.IsInducing.subtypeVal.continuous_iff.2 (hz.matrix_elem a b)
  have he : ∀ g, GG.map f (s' g) = r' g := fun g => by rw [← hs']; rfl
  have hem : ∀ g a b, f ((s' g).mat a b) = (r' g).mat a b := fun g a b => by rw [← he]; rfl
  let s : Γ →* GG 3 ↥L.1 := (GG.map (TrivSqZeroExt.fstHom ↥L.1 ↥L.1 ↥L.1).toRingHom).comp s'
  have hsr : ∀ g, (s g).right = (r g).right := fun g => by
    have := (hdef g).1
    rw [← he] at this
    exact this
  have hsm : ∀ g, (s g).mat.map ι = (r g).mat := fun g => by
    ext a b
    rw [← hfst, ← hem, (hf _).1]; rfl
  have hs : ∀ g, GG.map ι (s g) = r g := fun g =>
    SemidirectProduct.ext (Units.ext (hsm g)) (hsr g)
  let z : Γ → Matrix (Fin 3) (Fin 3) ↥L.1 := fun g =>
    (s' g).mat.map TrivSqZeroExt.snd * (((s g).left⁻¹ : GL (Fin 3) ↥L.1) : Matrix (Fin 3) (Fin 3) ↥L.1)
  have hzs : ∀ g, z g * (s g).mat = (s' g).mat.map TrivSqZeroExt.snd := fun g => by
    simp only [z, GG.mat, Matrix.mul_assoc, Units.inv_mul, Matrix.mul_one]
  have hz : ∀ g, (z g).map ι = y g := fun g => by
    have h1 : (z g).map ι * (r g).mat = y g * (r g).mat := by
      rw [← hsm g, ← Matrix.map_mul, hzs, hsm]
      ext a b
      rw [← hsnd, ← hem, (hf _).2]; rfl
    exact (Units.mul_left_inj (r g).left).1 h1
  have had : ∀ g X, (adRep s g X).map ι = adRep r g (X.map ι) := fun g X => by
    have := rigloc_adFun ι (s g) X
    rw [hs] at this
    exact this
  have hcj : ∀ g a b, f ((conjBy h₁⁻¹ s' g).mat a b) = (conjBy h⁻¹ r' g).mat a b := fun g a b => by
    have := rigloc_conj f h₁⁻¹ s' g
    rw [map_inv, hh, hs'] at this
    rw [← this]; rfl
  have hcy : ∀ σ, Units.map f.toMonoidHom
      (UpperTheory.V.Loc.cycA l l (DualNumber ↥L.1) σ) = UpperTheory.V.Loc.cycA l l (DualNumber (PadicAlgCl l)) σ := fun σ => by
    apply Units.ext
    apply TrivSqZeroExt.ext
    · exact (hf _).1
    · exact (hf _).2
  have key : z ∈ UpperTheory.V.Loc.finiteCocycles φ (adRep s) := by
    refine rig_fin P φ hφ η hη s z s' h₁ (fun g => (hsr g).trans (hm g)) ?_ ?_ ?_ ?_ H hH hHη ?_ w hw ?_ ?_
    · exact hcont _ (by simp only [mats, hsm]; exact hr)
    · exact hcont _ (by simp only [hz]; exact hy)
    · intro g k
      apply hιm
      simp only []
      rw [Matrix.map_add _ (map_add ι), had, hz, hz, hz, hcoc g k]
    · intro g
      refine ⟨rfl, ?_⟩
      ext a b : 1
      apply TrivSqZeroExt.ext
      · exact (rigloc_mul (z g) (s g).mat a b).1.symm
      · refine Eq.trans ?_ (rigloc_mul (z g) (s g).mat a b).2.symm
        rw [hzs]; rfl
    · intro g hg a b hab
      apply hfi
      rw [hcj, hU g hg a b hab, map_zero]
    · intro g hg hI a
      apply hfi
      rw [hcj, hκ g hg hI a, ← hcy, ← map_zpow, Units.coe_map]; rfl
    · intro i j hij
      obtain ⟨g, hg, hne⟩ := hne i j hij
      refine ⟨g, hg, fun e => hne ?_⟩
      rw [← hcj, ← hcj, (hf _).1, (hf _).1]
      have e2 := congrArg ι e
      rw [map_mul] at e2
      have e3 : ι ((UpperTheory.V.Loc.cycA l l ↥L.1 (φ g) : (↥L.1)ˣ) : ↥L.1) =
          ((UpperTheory.V.Loc.cycA l l (PadicAlgCl l) (φ g) : (PadicAlgCl l)ˣ) : PadicAlgCl l) := rfl
      rw [e3] at e2
      exact e2
  have := UpperTheory.V.Loc.z1fCoef φ (adRep s) (adRep r) (L.1.val.toLinearMap.mapMatrix)
    (continuous_matrix fun a b => continuous_subtype_val.comp (continuous_id.matrix_elem a b)) had z key
  have e : y = fun g => (z g).map ι := funext fun g => (hz g).symm
  rw [e]
  exact this
