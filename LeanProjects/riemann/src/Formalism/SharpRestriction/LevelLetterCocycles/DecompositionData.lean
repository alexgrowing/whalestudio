import Formalism.SharpRestriction.LevelLetterCocycles.QuotientHomNonvanishingBound
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial Formalism.WeaklyAdmissibleFiltrations Module Formalism.MainNotions.N

namespace Formalism.MainNotions.TruncatedSeriesCountingIdentities

open Formalism.BasicNotions Formalism.BasicNotions.Loc

section Lit

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR)
    (LL O : Type) [Field LL] [Algebra Qp LL] [TopologicalSpace LL] [IsTopologicalRing LL]
    [CommRing O] [Algebra O LL]

def FontaineAt : Prop :=
  (∀ (A₀ A₁ A₂ : GRep G Qp LL O) (ι : A₀.V →ₗ[LL] A₁.V) (π : A₁.V →ₗ[LL] A₂.V),
    (∀ g x, ι (A₀.ρ g x) = A₁.ρ g (ι x)) → (∀ g x, π (A₁.ρ g x) = A₂.ρ g (π x)) →
    Function.Injective ι → Function.Surjective π → LinearMap.range ι = LinearMap.ker π →
    (IsCrys PD A₁.ρ → IsCrys PD A₀.ρ ∧ IsCrys PD A₂.ρ ∧
      ∀ (τ : K →ₐ[Qp] LL) (a : ℤ), multV PD A₁.ρ τ a = multV PD A₀.ρ τ a + multV PD A₂.ρ τ a) ∧
    ((∃ s : A₂.V →ₗ[LL] A₁.V, (∀ g x, s (A₂.ρ g x) = A₁.ρ g (s x)) ∧ ∀ x, π (s x) = x) →
      IsCrys PD A₀.ρ → IsCrys PD A₂.ρ → IsCrys PD A₁.ρ)) ∧
  (∀ (A A' : GRep G Qp LL O) (χ : G →* LLˣ), IsTwistRep χ A.ρ A'.ρ → IsCrys PD (WeaklyAdmissibleFiltrations.charRep χ) →
    IsCrys PD A.ρ → IsCrys PD A'.ρ ∧
      ∀ (τ : K →ₐ[Qp] LL) (a b : ℤ), IsJumpV PD (WeaklyAdmissibleFiltrations.charRep χ) τ b →
        multV PD A'.ρ τ (a + b) = multV PD A.ρ τ a) ∧
  (∀ (A A' : GRep G Qp LL O) (P : A.V →ₗ[LL] A'.V →ₗ[LL] LL), IsDual1 PD A.ρ A'.ρ P →
    IsCrys PD A.ρ → IsCrys PD A'.ρ) ∧
  (∀ A : GRep G Qp LL O, IsCrys PD A.ρ → IsDR PD A.ρ)

def bkBAt : Prop :=
  ∀ L1 : WeaklyAdmissibleFiltrations.Lattice (O := O) (WeaklyAdmissibleFiltrations.charRep (cycLL PD LL)), L1.T = LinearMap.range (Algebra.linearMap O LL) →
  ∀ (A A' : GRep G Qp LL O) (LA : WeaklyAdmissibleFiltrations.Lattice (O := O) A.ρ) (LA' : WeaklyAdmissibleFiltrations.Lattice (O := O) A'.ρ)
    (P : A.V →ₗ[LL] A'.V →ₗ[LL] LL), IsDR PD A.ρ → IsDualLat1 PD LA LA' P →
    (∀ c ∈ divisibleCocycles LA', (c ∈ HfD PD LA' ↔ ∀ d ∈ latticeFiniteCocycles PD LA, CobO PD L1 (cupLD LA' P d c))) ∧
    (∀ d ∈ latticeCocycles LA, (d ∈ latticeFiniteCocycles PD LA ↔
      ∀ c ∈ divisibleCocycles LA', c ∈ HfD PD LA' → CobO PD L1 (cupLD LA' P d c)))

def TateDualityH2Torsion : Prop :=
  ∀ L1 : WeaklyAdmissibleFiltrations.Lattice (O := O) (WeaklyAdmissibleFiltrations.charRep (cycLL PD LL)), L1.T = LinearMap.range (Algebra.linearMap O LL) →
    Nonempty (ReciprocityTheory.Def.H2 (repD L1) ⊤ ≃ₗ[O] (LL ⧸ L1.T))

variable {LL O}

def CcO (X : Type) [TopologicalSpace X] : Submodule O (X → LL) where
  carrier := {c | Continuous c ∧ ∀ x, c x ∈ Set.range (algebraMap O LL)}
  zero_mem' := ⟨continuous_const, fun _ => ⟨0, map_zero _⟩⟩
  add_mem' := by
    rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
    refine ⟨ha.add hb, fun x => ?_⟩
    obtain ⟨u, hu⟩ := ha' x
    obtain ⟨v, hv⟩ := hb' x
    exact ⟨u + v, by simp [hu, hv]⟩
  smul_mem' := by
    rintro c a ⟨ha, ha'⟩
    refine ⟨?_, fun x => ?_⟩
    · have h : (c • a) = fun x => algebraMap O LL c * a x := by
        funext x
        simp [Algebra.smul_def]
      rw [h]
      exact continuous_const.mul ha
    · obtain ⟨u, hu⟩ := ha' x
      exact ⟨c * u, by simp [hu, Algebra.smul_def]⟩

variable (LL O)

def twoCocyclesTwist : Submodule O (G × G → LL) :=
  CcO (O := O) (G × G) ⊓ (LinearMap.ker (ReciprocityTheory.Def.d2 (WeaklyAdmissibleFiltrations.charRep (cycLL PD LL)))).restrictScalars O

def twoCoboundariesTwist : Submodule O (G × G → LL) :=
  (CcO (O := O) G).map ((ReciprocityTheory.Def.d1 (WeaklyAdmissibleFiltrations.charRep (cycLL PD LL))).restrictScalars O)

def TateDualityH2Integral : Prop :=
  Nonempty ((↥(twoCocyclesTwist PD LL O) ⧸ (twoCoboundariesTwist PD LL O).submoduleOf (twoCocyclesTwist PD LL O)) ≃ₗ[O] O)

theorem bkBAt_of_core [TopologicalSpace Qp] (h : bkBCore PD) (hO : GoodO (Qp := Qp) LL O) :
    bkBAt PD LL O := h LL O hO

theorem tate_duality_h2_of_all_coefficients [TopologicalSpace Qp] (h : LocalTateTopDegree PD) (hO : GoodO (Qp := Qp) LL O) :
    TateDualityH2Torsion PD LL O := h LL O hO

end Lit

variable (D : D7)

structure Decl (i : D.nd.Loc) where
  row : Finset (HeightOneSpectrum (𝓞 D.host.E))
  col : Finset (HeightOneSpectrum (𝓞 D.host.E))
  disj : Disjoint row col
  cover : ∀ v, (v ∈ row ∨ v ∈ col) ↔ v ∈ placesOver D.host.E (D.nd.l i)

structure CoefExt (i : D.nd.Loc) (w : HeightOneSpectrum (𝓞 D.host.E))
    (hw : w ∈ placesOver D.host.E (D.nd.l i)) where
  LL : FinExt (D.nd.l i)
  le : (D.nbr i w hw).LL.1 ≤ LL.1

variable {D}

def CoefExt.self (i : D.nd.Loc) (w : HeightOneSpectrum (𝓞 D.host.E))
    (hw : w ∈ placesOver D.host.E (D.nd.l i)) : CoefExt D i w hw where
  LL := (D.nbr i w hw).LL
  le := le_rfl

section AtW

variable {i : D.nd.Loc} {w : HeightOneSpectrum (𝓞 D.host.E)}
  {hw : w ∈ placesOver D.host.E (D.nd.l i)} (C : CoefExt D i w hw)

abbrev CoefExt.inc : Br.LL D.nbr i w hw →+* ↥C.LL.1 := (IntermediateField.inclusion C.le).toRingHom

abbrev locC {k : ℕ} (M : GE D.nd →* Matrix (Fin k) (Fin k) (D.nd.O i)) :
    Br.G D.nbr i w hw →* Matrix (Fin k) (Fin k) ↥C.LL.1 :=
  mapM C.inc (Br.loc D.nbr i w hw M)

abbrev chi1C : Br.G D.nbr i w hw →* (↥C.LL.1)ˣ :=
  (Units.map C.inc.toMonoidHom).comp (Br.locChi D.nbr i w hw (chiU D.nd i 1))

def CoefExt.IsGood : Prop := GoodCoef D.host.condN C.LL

theorem CoefExt.split (τ : ↥(D.nbr i w hw).Kw.1 →ₐ[ℚ_[D.nd.l i]] Om (D.nd.l i)) (x : ↥(D.nbr i w hw).Kw.1) :
    τ x ∈ C.LL.1 := C.le ((D.nbr i w hw).LL_split τ x)

theorem CoefExt.isGood : C.IsGood := (D.self_good i w hw).mono C.le

private lemma mem_LL_of_GoodCoef_of_le_Ks {l : ℕ} [Fact l.Prime] (K LL : FinExt l) (N : ℕ)
    (hg : GoodCoef N LL) (hsp : ∀ (τ : ↥K.1 →ₐ[ℚ_[l]] Om l) (x : ↥K.1), τ x ∈ LL.1)
    (hle : K.1 ≤ Ks K 1) (τ : ↥(Ks K 1) →ₐ[ℚ_[l]] Om l) (x : ↥(Ks K 1)) : τ x ∈ LL.1 := by
  set S : IntermediateField ℚ_[l] ↥(Ks K 1) := (LL.1).comap τ with hSdef
  have hT : Ks K 1 ≤ S.map (Ks K 1).val := by
    have hK : K.1 ≤ S.map (Ks K 1).val := by
      intro y hy
      exact ⟨⟨y, hle hy⟩, hsp (τ.comp (IntermediateField.inclusion hle)) ⟨y, hy⟩, rfl⟩
    have hA : IntermediateField.adjoin ℚ_[l] {x : Om l | x ^ (l ^ 1) = 1} ≤ S.map (Ks K 1).val := by
      rw [IntermediateField.adjoin_le_iff]
      intro y hy
      have hyK : y ∈ Ks K 1 :=
        (le_sup_right : IntermediateField.adjoin ℚ_[l] {x : Om l | x ^ (l ^ 1) = 1} ≤ K0 K ⊔ _)
          (IntermediateField.subset_adjoin _ _ hy)
      have hy' : y ^ l = 1 := by simpa using hy
      have h1 : (⟨y, hyK⟩ : ↥(Ks K 1)) ^ l = 1 := Subtype.ext (by simpa using hy')
      have hpow : (τ ⟨y, hyK⟩) ^ Nat.lcm l N = 1 := by
        obtain ⟨c, hc⟩ := Nat.dvd_lcm_left l N
        rw [hc, pow_mul, ← map_pow τ, h1, map_one, one_pow]
      exact ⟨⟨y, hyK⟩, hg _ hpow, rfl⟩
    show K0 K ⊔ IntermediateField.adjoin ℚ_[l] {x : Om l | x ^ (l ^ 1) = 1} ≤ _
    exact sup_le ((inf_le_left : K0 K ≤ K.1).trans hK) hA
  obtain ⟨z, hz, hzx⟩ := hT x.2
  have hzx' : z = x := Subtype.ext hzx
  rw [← hzx']
  exact hz

theorem CoefExt.IsGood.good_one {C : CoefExt D i w hw} (h : C.IsGood) (h2 : D.nd.l i ≠ 2)
    (hle : (D.nbr i w hw).Kw.1 ≤ Ks (D.nbr i w hw).Kw 1) : Good (D.nbr i w hw).Kw 1 C.LL := by
  delta Good
  refine ⟨le_rfl, fun h' => absurd h' h2, hle, ?_⟩
  intro τ x
  exact mem_LL_of_GoodCoef_of_le_Ks _ _ _ h C.split hle τ x

end AtW

open Classical

section Pt

variable (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i)))
  (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i) (dc : Decl D i)

def lenW (lenRow : HeightOneSpectrum (𝓞 D.host.E) → ℚ) (e' : HeightOneSpectrum (𝓞 D.host.E) → ℕ)
    (w : HeightOneSpectrum (𝓞 D.host.E)) : ℚ :=
  if h : w ∈ dc.col then Br.lenCol D.loc D.nbr i w ((dc.cover w).1 (Or.inr h)) ρ π (e' w) else lenRow w

def admG1 : Prop :=
  ∀ (g : GE D.nd) (k : ℕ), (fun x : D.nd.X i => ((rO D.nd i r x g).charpolyRev).coeff k) ∈ D.nd.T i

def admG2 : Prop :=
  ∀ (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i))
    (C : CoefExt D i w hw),
    GainBoundAt (Br.PD D.loc D.nbr i w hw) (fun x => locC C (rO D.nd i r x)) (chi1C C)
      D.R.t (fun c => locC C (chiRatO D.nd i c)) (locC C (WpO D.nd i ρ π)) (locC C (T2O D.nd i ρ π)) ∧
    ∀ x, IsCrys (Br.PD D.loc D.nbr i w hw) (matRep (twistM (locC C (rO D.nd i r x)) (chi1C C)⁻¹))

def admG3 : Prop :=
  (∀ x, AbsIrrDistinct (repK D.nd i r x)) ∧
  (∀ x (g : GE D.nd), (mapM (IsLocalRing.residue (D.nd.O i)) (rO D.nd i r x) g).charpoly =
    (mapM (IsLocalRing.residue (D.nd.O i)) (rhoO D.nd i ρ π) g).charpoly *
      ∏ c ∈ Finset.Icc 1 D.R.t, (X - C (IsLocalRing.residue (D.nd.O i) ((chiU D.nd i c g : (D.nd.O i)ˣ) : D.nd.O i)))) ∧
  Submodule.span (kk D.nd i) (Set.range (mapM (IsLocalRing.residue (D.nd.O i)) (rhoO D.nd i ρ π))) = ⊤

def admG4 : Prop :=
  ∀ (x : D.nd.X i) (v : HeightOneSpectrum (𝓞 D.host.E)),
    v ∉ placesOver D.host.E (D.nd.l i) → v ∉ D.nd.S i → v ∉ D.nd.Q i →
      ∀ g ∈ Ine (F := D.host.E) (D.nd.plOm.1 v), r x g = 1

def admG5 : Prop :=
  ∀ w : HeightOneSpectrum (𝓞 D.host.E), (w ∈ D.nd.S i ∨ w ∈ D.nd.Q i) →
    ((w ∈ D.nd.Q i ∨ w ∈ placesOver D.host.E D.host.pde ∨
        (D.nd.l i = D.host.pde ∧ w ∈ placesOver D.host.E D.host.pde')) → ∀ x,
      (∀ γ ∈ Ine (F := D.host.E) (D.nd.plOm.1 w),
        (((r x γ : GL _ _) : Matrix (Fin D.R.nV) (Fin D.R.nV) (D.nd.O i)) - 1) *
          (((r x γ : GL _ _) : Matrix (Fin D.R.nV) (Fin D.R.nV) (D.nd.O i)) - chi1 D.nd i γ • 1) = 0) ∧
      ∃ Pm : GL (Fin D.R.nV) (KK D.nd i), ∀ γ ∈ Ine (F := D.host.E) (D.nd.plOm.1 w),
        ((Pm⁻¹ * mapRep (algebraMap (D.nd.O i) (KK D.nd i)) (r x) γ * Pm : GL _ _) :
          Matrix (Fin D.R.nV) (Fin D.R.nV) (KK D.nd i)) =
        Matrix.diagonal (fun k : Fin D.R.nV =>
          if (k : ℕ) < D.R.r then 1 else algebraMap (D.nd.O i) (KK D.nd i) (chi1 D.nd i γ))) ∧
    ((∃ k, w ∈ placesOver D.host.E (D.host.g k)) → w ∈ D.nd.S i →
      TameGen D.nd (D.nd.plOm.1 w) (D.nd.gam0 i w) →
      ∃ Pp : Polynomial (D.nd.T i),
        IsUnit (Pp.eval (algebraMap (D.nd.O i) (D.nd.T i) (chi1 D.nd i (D.nd.gam0 i w)))) ∧
        ∀ x, ∀ γ ∈ Ine (F := D.host.E) (D.nd.plOm.1 w),
          Polynomial.aeval ((r x (D.nd.gam0 i w) : GL _ _) : Matrix (Fin D.R.nV) (Fin D.R.nV) (D.nd.O i))
              (Pp.map ((Pi.evalRingHom (fun _ : D.nd.X i => D.nd.O i) x).comp (D.nd.T i).val.toRingHom)) *
            (((r x γ : GL _ _) : Matrix (Fin D.R.nV) (Fin D.R.nV) (D.nd.O i)) - chi1 D.nd i γ • 1) = 0)

def TameGeneratorConditions : Prop :=
  ∀ v : HeightOneSpectrum (𝓞 D.host.E), v ∈ D.nd.S i ∨ v ∈ D.nd.Q i →
    TameGen D.nd (D.nd.plOm.1 v) (D.nd.gam0 i v) ∧
    (∀ c ∈ Finset.Icc 1 D.R.t, ∀ g ∈ Ine (F := D.host.E) (D.nd.plOm.1 v), D.nd.chi i c g = D.nd.chi i 1 g) ∧
    (v ∈ D.nd.Q i → D.nd.zeta i v ≠ 1) ∧
    (v ∈ D.nd.S i → (v ∈ placesOver D.host.E D.host.pde ∨
        (D.nd.l i = D.host.pde ∧ v ∈ placesOver D.host.E D.host.pde')) → IsUnit (D.nd.zeta i v - 1))

def admG6 : Prop :=
  ∀ x : D.nd.X i,
    (∃ u : Fin D.R.nV → KK D.nd i, u ≠ 0 ∧
      ∀ g, (mapM (toK D.nd i) (rO D.nd i r x) g).mulVec u = toK D.nd i ((chiU D.nd i 1 g : (D.nd.O i)ˣ) : D.nd.O i) • u) →
      x ∈ D.nd.Z i

def admBK : Prop :=
  ∀ (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i))
    (C : CoefExt D i w hw),
    TateDualityH2Torsion (Br.PD D.loc D.nbr i w hw) ↥C.LL.1 ↥(OL C.LL) ∧
    BlochKatoDim (Br.PD D.loc D.nbr i w hw) ↥C.LL.1 ∧
    (C.IsGood → bkBAt (Br.PD D.loc D.nbr i w hw) ↥C.LL.1 ↥(OL C.LL))

def admTB (cB : ℕ) : Prop :=
  ∀ (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i))
    (C : CoefExt D i w hw), C.IsGood →
    TBAt (Br.PD D.loc D.nbr i w hw) (O := ↥(OL C.LL)) (Br.inert D.nbr i w hw)
      (fun τ => {a | IsJumpV (Br.PD D.loc D.nbr i w hw) (matRep (locC C (rTwO D.nd i r π))) τ a}) D.R.t cB

def LengthBoundAtPlaces (lenRow : HeightOneSpectrum (𝓞 D.host.E) → ℚ) : Prop :=
  ∀ (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i)), w ∈ dc.row →
    ∀ C : CoefExt D i w hw, C.IsGood →
    RowAt (Br.PD D.loc D.nbr i w hw) (O := ↥(OL C.LL)) (fun x : D.nd.X i => ⇑(locC C (rDuO D.nd i r x)))
      ⇑(locC C (T2O D.nd i ρ π)) (lenRow w)

def LiftExponentAtPlaces (e' : HeightOneSpectrum (𝓞 D.host.E) → ℕ) : Prop :=
  ∀ (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i)), w ∈ dc.col →
    ∀ C : CoefExt D i w hw, C.IsGood →
    LiftAt (Br.PD D.loc D.nbr i w hw) (O := ↥(OL C.LL)) (fun x : D.nd.X i => ⇑(locC C (rTwO D.nd i r x)))
      (e' w)

def FamilyContinuous : Prop := ∀ x : D.nd.X i, Continuous (fun g => rO D.nd i r x g)

def admSS : Prop := ∀ x : D.nd.X i, IsSS (repK D.nd i r x)

def SemisimpleDecomposition : Prop :=
  ∃ e : (Fin D.R.nV → KK D.nd i) ≃ₗ[KK D.nd i] ((Fin D.R.r → KK D.nd i) × (Fin D.R.t → KK D.nd i)),
    ∀ g u, e ((mapM (toK D.nd i) (rO D.nd i r π) g).mulVec u) =
      ((mapM (toK D.nd i) (rhoO D.nd i ρ π) g).mulVec (e u).1,
        fun c : Fin D.R.t => toK D.nd i ((chiU D.nd i ((c : ℕ) + 1) g : (D.nd.O i)ˣ) : D.nd.O i) * (e u).2 c)

def CyclotomicInertiaImage : Prop :=
  ∃ w ∈ placesOver D.host.E (D.nd.l i), ∀ z : ℤ_[D.nd.l i],
    ∃ g ∈ Ine (F := D.host.E) (D.nd.plOm.1 w),
      ((cycZ (F := D.host.E) (Ω := D.nd.Om) (D.nd.l i) g : ℤ_[D.nd.l i]ˣ) : ℤ_[D.nd.l i]) =
        1 + (D.nd.l i : ℤ_[D.nd.l i]) ^ D.nd.s0 i * z

def LocalCoefficientCompatibility : Prop :=
  ∀ (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i)),
    Br.EOAlg (D.nbr i w hw) ∧ Br.EOTop (D.nbr i w hw) ∧ Br.DegW D.nbr i w hw

def CyclotomicCompletionAdmissible : Prop :=
  ∀ (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i)),
    (D.nbr i w hw).Kw.1 ≤
      IntermediateField.adjoin ℚ_[D.nd.l i] {x : Om (D.nd.l i) | x ^ Nat.lcm (D.nd.l i) D.host.condN = 1}

def FontaineAtPlacesOverL : Prop :=
  ∀ (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i))
    (C : CoefExt D i w hw), FontaineAt (Br.PD D.loc D.nbr i w hw) ↥C.LL.1 ↥(OL C.LL)

def admH2 : Prop :=
  ∀ (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i))
    (C : CoefExt D i w hw), TateDualityH2Integral (Br.PD D.loc D.nbr i w hw) ↥C.LL.1 ↥(OL C.LL)

def unrHom : Submodule (D.nd.O i) (GE D.nd → KmodO (D.nd.O i)) where
  carrier := {c | IsLocallyConstant c ∧ (∀ g h, c (g * h) = c g + c h) ∧
    ∀ v : HeightOneSpectrum (𝓞 D.host.E), ∀ g ∈ Ine (F := D.host.E) (D.nd.plOm.1 v), c g = 0}
  zero_mem' := ⟨IsLocallyConstant.const 0, fun _ _ => by simp, fun _ _ _ => rfl⟩
  add_mem' := by
    rintro a b ⟨ha, ha', ha''⟩ ⟨hb, hb', hb''⟩
    refine ⟨ha.add hb, fun g h => ?_, fun v g hg => ?_⟩
    · simp only [Pi.add_apply, ha', hb']
      abel
    · simp only [Pi.add_apply, ha'' v g hg, hb'' v g hg, add_zero]
  smul_mem' := by
    rintro c a ⟨ha, ha', ha''⟩
    refine ⟨ha.comp (fun m => c • m), fun g h => ?_, fun v g hg => ?_⟩
    · simp only [Pi.smul_apply, ha', smul_add]
    · simp only [Pi.smul_apply, ha'' v g hg, smul_zero]

def UnramifiedClassFieldBound : Prop :=
  Module.length (D.nd.O i) ↥(unrHom i) < ⊤ ∧
    lenUnit (O := D.nd.O i) (D.nd.l i) ↥(unrHom i) ≤ (padicValNat (D.nd.l i) (Formalism.MainNotions.N.hE D.host) : ℚ)

def admitted (lenRow : HeightOneSpectrum (𝓞 D.host.E) → ℚ) (e' : HeightOneSpectrum (𝓞 D.host.E) → ℕ)
    (cB : ℕ) : Prop :=
  admG1 i r ∧ admG2 i r ρ π ∧ admG3 i r ρ π ∧ admG4 i r ∧ admG5 i r ∧ TameGeneratorConditions i ∧ admG6 i r ∧
    admBK i ∧ admTB i r π cB ∧ LengthBoundAtPlaces i r ρ π dc lenRow ∧ LiftExponentAtPlaces i r dc e' ∧
    FamilyContinuous i r ∧ admSS i r ∧ SemisimpleDecomposition i r ρ π ∧ CyclotomicInertiaImage i ∧
    LocalCoefficientCompatibility i ∧ CyclotomicCompletionAdmissible i ∧ FontaineAtPlacesOverL i ∧ admH2 i ∧ UnramifiedClassFieldBound i

def GlobalLatticeIndexTheorem (lenRow : HeightOneSpectrum (𝓞 D.host.E) → ℚ) (e' : HeightOneSpectrum (𝓞 D.host.E) → ℕ)
    (cB : ℕ) : Prop :=
  D.nd.l i ≠ D.host.g 0 → D.nd.l i ≠ D.host.g 1 → π ∈ D.nd.Z i →
    Br.sFin D.loc D.nbr i ρ π →
    (∀ e ∈ Finset.Ioo 0 D.R.t, Formalism.GaloisCohomology.shaLen (D.nd.ldat (D.nd.l i)) (e : ℤ) < ⊤) →
    D.nd.vcc i π ≤
      (∑ w ∈ dc.row ∪ dc.col, lenW i ρ π dc lenRow e' w) + Br.sPi D.loc D.nbr i ρ π +
      (∑ e ∈ Finset.Ioo 0 D.R.t, D.what₂.shaLen (D.nd.l i) e) +
      (padicValNat (D.nd.l i) (Formalism.MainNotions.N.hE D.host) : ℚ) +
      (D.R.t : ℚ) * (∑ w ∈ dc.row, ((Formalism.MainNotions.N.locDeg D.host.E w : ℚ) + 2) * (cB : ℚ)) +
      4 * (D.R.nV : ℚ) * ((dc.col.card : ℚ) + 1) * D.nd.vdel i +
      (D.R.t : ℚ) * (dc.col.card : ℚ) * h0 D.nd i dc.col +
      (D.R.t : ℚ) * (∑ v ∈ D.nd.Q i, lenUnit (O := D.nd.O i) (D.nd.l i) (D.nd.O i ⧸ Ideal.span {D.nd.zeta i v - 1}))

end Pt

def EndomorphismIndexBound (i : D.nd.Loc) : Prop :=
  ∀ Z' : Finset (D.nd.X i), Z' ⊆ D.nd.Z i →
    ∀ (α : Module.End (D.nd.O i) (D.nd.Mt i)) (A : ℤ), A ≠ 0 →
      (∀ f : D.nd.T i, α * D.nd.act i f = D.nd.act i f * α) →
      (∀ x ∈ Z', ∀ u ∈ heckeEig (D.nd.T i) (D.nd.act i) x,
        α.baseChange (KK D.nd i) u = (A : KK D.nd i) • u) →
      (∀ x ∈ D.nd.Z i, x ∉ Z' → ∀ u ∈ heckeEig (D.nd.T i) (D.nd.act i) x, α.baseChange (KK D.nd i) u = 0) →
      lenUnit (O := D.nd.O i) (D.nd.l i)
          (↥(MtUp D.nd i Z') ⧸ (MtLow D.nd i Z').comap (MtUp D.nd i Z').subtype) ≤
        ∑ π ∈ Z', (D.nd.mult i π : ℚ) * (D.nd.vcc i π + padicValInt (D.nd.l i) A)

def IntegralityFromMetric (D : D7) : Prop :=
  ∀ (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i)))
    (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i) (dc : Decl D i)
    (lenRow : HeightOneSpectrum (𝓞 D.host.E) → ℚ) (e' : HeightOneSpectrum (𝓞 D.host.E) → ℕ) (cB : ℕ),
    GoodR D.nd i r → admitted i r ρ π dc lenRow e' cB → GlobalLatticeIndexTheorem i ρ π dc lenRow e' cB

def HodgeTateFromSandwich (D : D7) : Prop := ∀ i : D.nd.Loc, EndomorphismIndexBound i

def Stmt (D : D7) : Prop := IntegralityFromMetric D ∧ HodgeTateFromSandwich D

end Formalism.MainNotions.TruncatedSeriesCountingIdentities
