import Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.NormsAndPolarizations.CjApply
open IsLocalRing Matrix NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal UpperTheory.V UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa UpperTheory.V.HV UpperTheory.V.Th UpperTheory.V.Th.Nm GlobalTheory.GalOfCusp

private theorem inc_local {l : ℕ} [Fact l.Prime] {c c' : Coef l} (h : c.O ≤ c'.O) : IsLocalHom (inc h) := by
  have hint : (inc h).IsIntegral := by
    have h0 : (algebraMap ℤ_[l] c'.O).IsIntegral := fun x => Algebra.IsIntegral.isIntegral x
    have e : (inc h).comp (algebraMap ℤ_[l] c.O) = algebraMap ℤ_[l] c'.O := by
      ext a; rfl
    rw [← e] at h0
    exact RingHom.IsIntegral.tower_top _ _ h0
  exact RingHom.IsIntegral.isLocalHom hint (Subalgebra.inclusion_injective h)

private theorem pushCh_ker {H A B : Type} [Group H] [CommRing A] [CommRing B] (f : A →+* B) (hf : Function.Injective f)
    (χ : H →* Aˣ) : (pushCh f χ).ker = χ.ker := by
  ext g
  simp only [MonoidHom.mem_ker, MonoidHom.comp_apply]
  constructor
  · intro hg
    apply Units.ext
    apply hf
    have := congrArg Units.val hg
    simpa using this
  · intro hg
    rw [hg, map_one]

private theorem polar_push {l : ℕ} [Fact l.Prime] {n : ℕ} (F : GFrame l) {O O' k k' : Type} [CommRing O] [CommRing O']
    [CommRing k] [CommRing k'] [Algebra ℤ_[l] O] [Algebra ℤ_[l] O'] [Algebra O k] [Algebra O' k']
    (i : O →+* O') (f : k →+* k') (hi : ∀ a, i (algebraMap ℤ_[l] O a) = algebraMap ℤ_[l] O' a)
    (hf : ∀ a, f (algebraMap O k a) = algebraMap O' k' (i a)) (χ : Fin n → F.G₀ →* kˣ)
    (hp : F.IsPolar O (GDet.ofRep (diagRep χ))) :
    F.IsPolar O' (GDet.ofRep (diagRep fun j => pushCh f (χ j))) := by
  intro B _ _ _ _ y
  letI : Algebra k B := ((algebraMap k' B).comp f).toAlgebra
  letI : Algebra O B := ((algebraMap O' B).comp i).toAlgebra
  haveI : IsScalarTower O k B := IsScalarTower.of_algebraMap_eq fun a => by
    change algebraMap O' B (i a) = algebraMap k' B (f (algebraMap O k a))
    rw [hf, ← IsScalarTower.algebraMap_apply]
  have he : F.eps O' B = F.eps O B := by
    unfold GFrame.eps
    congr 1
    ext a
    change algebraMap O' B (algebraMap ℤ_[l] O' a) = algebraMap O' B (i (algebraMap ℤ_[l] O a))
    rw [hi]
  have hs : F.star O' B n y = F.star O B n y := by
    unfold GFrame.star GFrame.starOp
    simp only [he]
  have hr : GDet.repAlg (diagRep fun j => pushCh f (χ j)) B = GDet.repAlg (diagRep χ) B := by
    unfold GDet.repAlg
    congr 1
    ext g a b
    by_cases hab : a = b
    · subst hab
      simp [diagRep]
      rfl
    · simp [diagRep, hab]
  have := hp B y
  change (GDet.repAlg (diagRep χ) B _).det = (GDet.repAlg (diagRep χ) B _).det at this
  change (GDet.repAlg (diagRep fun j => pushCh f (χ j)) B _).det = (GDet.repAlg (diagRep fun j => pushCh f (χ j)) B _).det
  rw [hr, hs]
  exact this

theorem UpperTheory.V.Th.Nm.residPush :
    ∀ {l : ℕ} [Fact l.Prime] {n : ℕ} (F : GFrame l) (c c' : Coef l) (h : c.O ≤ c'.O) (r : Resid F c.O n), ∃ r' : Resid F c'.O n, RPush h r r' ∧ (∀ u, r'.Ip u = r.Ip u) ∧ (r.V0ok → r'.V0ok) := by
  intro l _ n F c c' h r
  haveI := inc_local h
  let f : ResidueField c.O →+* ResidueField c'.O := ResidueField.map (inc h)
  have hfi : Function.Injective f := f.injective
  have hf : ∀ a, f (residue c.O a) = residue c'.O (inc h a) := fun a => ResidueField.map_residue _ a
  refine ⟨{ chib := fun i => pushCh f (r.chib i)
            chib_open := fun i => by rw [pushCh_ker f hfi]; exact r.chib_open i
            chib_inj := fun i j hij => r.chib_inj ?_
            polar := polar_push F (inc h) f (fun _ => rfl) hf r.chib r.polar
            psib := fun v i => pushCh f (r.psib v i)
            psib_open := fun v i => by rw [pushCh_ker f hfi]; exact r.psib_open v i
            th := fun v i => pushCh (inc h) (r.th v i)
            th_comm := fun v i g hg => by
              rw [MonoidHom.comp_apply, r.th_comm v i g hg, map_one] },
    ⟨f, hf, fun _ => rfl, fun _ _ => rfl, fun _ _ => rfl⟩, fun u => ?_, fun hv => ⟨fun i => ?_, fun g hg i j => ?_, ?_⟩⟩
  · ext g
    apply hfi
    have := congrArg Units.val (DFunLike.congr_fun hij g)
    simpa using this
  · simp only [Resid.Ip, pushCh_ker f hfi]
  · rw [pushCh_ker f hfi]; exact hv.1 i
  · change Units.map _ (r.chib i g) = Units.map _ (r.chib j g)
    rw [hv.2.1 g hg i j]
  · obtain ⟨g, hg, hne⟩ := hv.2.2
    refine ⟨g, hg, fun e => hne ?_⟩
    apply Units.ext
    apply hfi
    have := congrArg Units.val e
    rw [Units.val_one, map_one]
    exact (hf _).trans this
