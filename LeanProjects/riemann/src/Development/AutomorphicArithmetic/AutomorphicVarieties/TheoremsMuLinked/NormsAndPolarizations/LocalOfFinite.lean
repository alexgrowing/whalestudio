import Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.NormsAndPolarizations.CjApply
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.DGmap
import Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.NormsAndPolarizations.InOfIntIff
import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.CopNormLt
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.DGext
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.LocalRingsCompletion.dvrFinite
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.PatchingBaseChange.PairBc

open IsLocalRing Matrix NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal UpperTheory.V UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa UpperTheory.V.HV UpperTheory.V.Th UpperTheory.V.Th.Nm GlobalTheory.GalOfCusp

private theorem local_of_finite {R S : Type} [CommRing R] [IsLocalRing R] [CommRing S] [IsLocalRing S]
    [Finite (ResidueField S)] (f : R →+* S) : IsLocalHom f := by
  classical
  constructor
  intro a ha
  by_contra hna
  have hm : a ∈ maximalIdeal R := hna
  let g : R →+* ResidueField S := (residue S).comp f
  have hker : RingHom.ker g = maximalIdeal R := by
    haveI : (RingHom.ker g).IsPrime := RingHom.ker_isPrime g
    haveI : Finite (R ⧸ RingHom.ker g) := Finite.of_injective _ (RingHom.kerLift_injective g)
    have hmax : (RingHom.ker g).IsMaximal :=
      Ideal.Quotient.maximal_of_isField _ (Finite.isField_of_domain _)
    exact IsLocalRing.eq_maximalIdeal hmax
  have hg : g a = 0 := by
    rw [← RingHom.mem_ker, hker]
    exact hm
  have hfa : f a ∈ maximalIdeal S := by
    simpa [g, residue_eq_zero_iff] using hg
  exact hfa ha

theorem UpperTheory.V.Th.Nm.redOf :
    ∀ {l : ℕ} [Fact l.Prime] {n : ℕ} (F : GFrame l) (c c' : Coef l) (h : c.O ≤ c'.O) (r : Resid F c.O n) (r' : Resid F c'.O n) (R : Type) [CommRing R] [Algebra c.O R] [IsCO c.O R] (p : Pair r R) (x : R →ₐ[c.O] Qbar l) (ρ₀ : F.G₀ →* GL (Fin n) c'.O) (ψ₀ : ∀ v, Fin n → F.Gv v →* c'.Oˣ), RPush h r r' → (∀ b, x b ∈ c'.O) → p.D.map (x : R →+* Qbar l) = GDet.ofRep (mat (pushRep (algebraMap c'.O (Qbar l)) ρ₀)) → (∀ v i, pushCh (algebraMap c'.O (Qbar l)) (ψ₀ v i) = pushCh (x : R →+* Qbar l) (p.ψ v i)) → (GDet.ofRep (mat ρ₀)).map (res c'.O c'.O : c'.O →+* ResidueField c'.O) = r'.Dbar ∧ ∀ v i, r'.IsPsi v i (ψ₀ v i) := by
  intro l _ n F c c' h r r' R _ _ _ p x ρ₀ ψ₀ hpush hx hD hψ
  haveI : Module.Finite ℤ_[l] c'.O := c'.fin
  haveI : Finite (ResidueField c'.O) := (abelian₂.dvr_finite l c'.O).2.1
  obtain ⟨f, hf, hchi, hpsi, hth⟩ := hpush
  let ι : c'.O →+* Qbar l := algebraMap c'.O (Qbar l)
  have hι : Function.Injective ι := Subtype.val_injective
  let y : R →+* c'.O := (x : R →+* Qbar l).codRestrict c'.O hx
  have hy : ι.comp y = (x : R →+* Qbar l) := by
    ext z
    rfl
  haveI : IsLocalHom y := local_of_finite y
  have hyalg : ∀ a : c.O, y (algebraMap c.O R a) = inc h a := by
    intro a
    apply hι
    show x (algebraMap c.O R a) = ι (inc h a)
    rw [x.commutes]
    rfl
  have hym : ∀ z ∈ maximalIdeal R, y z ∈ maximalIdeal c'.O := by
    intro z hz
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    intro hu
    exact hz ((isUnit_map_iff y _).1 hu)
  have hres : ∀ z, residue c'.O (y z) = f (res c.O R z) := by
    intro z
    obtain ⟨a, ha⟩ := IsCO.res_surj (O := c.O) z
    have hz : z = algebraMap c.O R a + (z - algebraMap c.O R a) := by ring
    have hm0 : res c.O R (z - algebraMap c.O R a) = 0 := by
      simp [UpperTheory.V.Alg.res, (IsLocalRing.residue_eq_zero_iff _).2 ha]
    have hm1 : residue c'.O (y (z - algebraMap c.O R a)) = 0 :=
      (IsLocalRing.residue_eq_zero_iff _).2 (hym _ ha)
    rw [hz, map_add, map_add, map_add, hm1, hm0, hyalg, AlgHom.commutes, ← hf]
    simp [ResidueField.algebraMap_eq]
  have hresid : ∀ w : c'.O, res c'.O c'.O w = residue c'.O w := by
    intro w
    have := (res c'.O c'.O).commutes w
    simpa [ResidueField.algebraMap_eq] using this
  have hresring : (res c'.O c'.O : c'.O →+* ResidueField c'.O) = residue c'.O := by
    ext w
    exact hresid w
  have hmapeq : (GDet.ofRep (mat ρ₀)).map ι = (p.D.map y).map ι := by
    rw [(CA.d_gmap (p.D)).2.1 y ι, hy, hD, (CA.d_gmap (GDet.ofRep (mat ρ₀))).2.2.2 ι (mat ρ₀)]
    congr 1
  have hρ : GDet.ofRep (mat ρ₀) = p.D.map y := by
    apply CA.d_gext
    intro g i _ _
    apply hι
    have e1 := ((CA.d_gmap (GDet.ofRep (mat ρ₀))).2.2.1 ι (MonoidAlgebra.single g 1)).2 i
    have e2 := ((CA.d_gmap (p.D.map y)).2.2.1 ι (MonoidAlgebra.single g 1)).2 i
    rw [← e1, ← e2, hmapeq]
  have hψy : ∀ v i g, ((ψ₀ v i g : c'.Oˣ) : c'.O) = y (p.ψ v i g : R) := by
    intro v i g
    apply hι
    have := congrArg (fun φ : F.Gv v →* (Qbar l)ˣ => ((φ g : (Qbar l)ˣ) : Qbar l)) (hψ v i)
    exact this
  refine ⟨?_, ?_⟩
  · rw [hρ, (CA.d_gmap p.D).2.1, hresring]
    have hcomp : (residue c'.O).comp y = f.comp (res c.O R : R →+* ResidueField c.O) := by
      ext z
      exact hres z
    rw [hcomp, ← (CA.d_gmap p.D).2.1, p.red]
    show (GDet.ofRep (diagRep r.chib)).map f = GDet.ofRep (diagRep r'.chib)
    rw [(CA.d_gmap (GDet.ofRep (diagRep r.chib))).2.2.2 f (diagRep r.chib)]
    congr 1
    ext g i j
    simp only [MonoidHom.coe_comp, Function.comp_apply, diagRep, MonoidHom.coe_mk, OneHom.coe_mk,
      RingHom.coe_coe, RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.diagonal_apply, hchi]
    split_ifs with hij <;> simp [hij, Matrix.diagonal_apply]
  · intro v i
    refine ⟨?_, ?_, ?_⟩
    · intro N
      have hle : maximalIdeal R ^ N ≤ (maximalIdeal c'.O ^ N).comap y := by
        rw [← Ideal.map_le_iff_le_comap, Ideal.map_pow]
        exact Ideal.pow_right_mono (Ideal.map_le_iff_le_comap.2 hym) N
      have hc := (p.psi v i).cont N
      have : (fun g => Ideal.Quotient.mk (maximalIdeal c'.O ^ N) ((ψ₀ v i g : c'.Oˣ) : c'.O)) =
          (Ideal.quotientMap (maximalIdeal c'.O ^ N) y hle) ∘
            (fun g => Ideal.Quotient.mk (maximalIdeal R ^ N) ((p.ψ v i g : Rˣ) : R)) := by
        funext g
        simp [hψy, Ideal.quotientMap_mk]
      rw [this]
      exact hc.comp _
    · intro g
      rw [hresid, hψy, hres, (p.psi v i).red, hpsi]
      rfl
    · intro g
      rw [hψy, (p.psi v i).mu, hyalg, hth]
      rfl
