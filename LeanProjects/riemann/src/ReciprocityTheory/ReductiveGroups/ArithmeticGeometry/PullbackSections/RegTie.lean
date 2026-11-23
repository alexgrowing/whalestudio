import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.GermExCut
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.UnifAt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc

set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.PullbackSections

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.L2.Pj
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor

attribute [local instance] Over.cartesianMonoidalCategory

section Comparison₂

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {V : Type} [CommRing V] [IsDomain V]

def SecTieK {t : SAB H (Sp V)} {tK : SAB H (Sp (FractionRing V))} (m : SABMap tK t (Out.jK V))
    (w : LB.Iso tK.PP.L (t.PP.L.pull m.φ)) (k : ℕ)
    (F : LB.Sec (LPow tK.G tK.PP.L (k : ℤ) (𝟙_ (Over (Sp (FractionRing V))))))
    (σ : LB.Sec (LB.LinComb t.PP.L (K := Fin 1) (fun _ => 𝟙 t.G.left) (fun _ => (k : ℤ)))) : Prop :=
  ∀ (Z : Scheme.{0}) (r : Z ⟶ tK.G.left) (zp : Z ⟶ (𝟙_ (Over (Sp (FractionRing V))) ⊗ tK.G).left),
    zp ≫ (snd (𝟙_ (Over (Sp (FractionRing V)))) tK.G).left = r →
    ∀ (z : Z) (J : (Z ⟶ t.G.left) → t.PP.L.ι) (J' : (Z ⟶ tK.G.left) → tK.PP.L.ι),
      Good t.PP.L z J → Good tK.PP.L z J' →
      sval σ (r ≫ m.φ) z J = ((gv w r z (fun _ => J (r ≫ m.φ)) (J' (r ≫ 𝟙 _))).val) ^ k * sval F zp z J'

end Comparison₂

def RegUnifSt : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (V : Type) [CommRing V] [IsDomain V]
    [IsDiscreteValuationRing V] [IsAdicComplete (IsLocalRing.maximalIdeal V) V] [CharZero V]
    (t : SAB H (Sp V)) (P : PELUnif (IsLocalRing.maximalIdeal V) t), P.TorsionIso →
    ∀ θ : LB.Sec (LB.LinComb t.PP.L (K := Fin 1) (fun _ => 𝟙 t.G.left) (fun _ => ((1 : ℕ) : ℤ))),
      (∀ σ : LB.Sec (LB.LinComb t.PP.L (K := Fin 1) (fun _ => 𝟙 t.G.left) (fun _ => ((1 : ℕ) : ℤ))),
        ∃! a : V, ∀ i, σ.f i = resG t.G.left le_top ((t.G.hom).appTop.hom (toΓ V a)) * θ.f i) →
    ∀ (M : ℕ), IsUnit (M : V) →
    ∀ (tK : SAB H (Sp (FractionRing V))) (m : SABMap tK t (Out.jK V)) (w : LB.Iso tK.PP.L (t.PP.L.pull m.φ)),
      RigIso m w →
    ∀ (θK : LB.Sec (LPow tK.G tK.PP.L ((1 : ℕ) : ℤ) (𝟙_ (Over (Sp (FractionRing V)))))), SecTieK m w 1 θK θ →
    ∀ (t₀ : 𝟙_ (Over (Sp (FractionRing V))) ⟶ tK.G)
      (F : LB.Sec (LPow tK.G tK.PP.L ((M : ℤ) ^ 2) (𝟙_ (Over (Sp (FractionRing V)))))),
      IsVtOver tK.G tK.PP M (fun u => u ^ (M ^ 2) = 1) (zCast tK.G (Nat.cast_one) θK) t₀ F →
      ∃ σ : LB.Sec (LB.LinComb t.PP.L (K := Fin 1) (fun _ => 𝟙 t.G.left) (fun _ => ((M ^ 2 : ℕ) : ℤ))),
        SecTieK m w (M ^ 2) (zCast tK.G (natCast_sq M) F) σ

section Move

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

def TieMv {X₀ : Scheme.{0}} {t₀ : SAB H X₀} {K : Type} [Field K] {x : Sp K ⟶ X₀} {tK : SAB H (Sp K)}
    (m1 : SABMap tK t₀ x) (w1 : LB.Iso tK.PP.L (t₀.PP.L.pull m1.φ)) (k : ℕ)
    (F : LB.Sec (LPow t₀.G t₀.PP.L (k : ℤ) (Over.mk x)))
    (FK : LB.Sec (LPow tK.G tK.PP.L (k : ℤ) (𝟙_ (Over (Sp K))))) : Prop :=
  ∀ (Z : Scheme.{0}) (r : Z ⟶ tK.G.left) (zp : Z ⟶ (Over.mk x ⊗ t₀.G).left)
    (zp' : Z ⟶ (𝟙_ (Over (Sp K)) ⊗ tK.G).left),
    zp ≫ (snd (Over.mk x) t₀.G).left = r ≫ m1.φ → zp ≫ (fst (Over.mk x) t₀.G).left = r ≫ tK.G.hom →
    zp' ≫ (snd (𝟙_ (Over (Sp K))) tK.G).left = r →
    ∀ (z : Z) (J : (Z ⟶ t₀.G.left) → t₀.PP.L.ι) (J' : (Z ⟶ tK.G.left) → tK.PP.L.ι),
      Good t₀.PP.L z J → Good tK.PP.L z J' →
      sval F zp z J = ((gv w1 r z (fun _ => J (r ≫ m1.φ)) (J' (r ≫ 𝟙 _))).val) ^ k * sval FK zp' z J'

end Move

def VtMoveSt : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (X₀ : Scheme.{0}) (t₀ : SAB H X₀)
    (K : Type) [Field K] (x : Sp K ⟶ X₀) (tK : SAB H (Sp K)) (m1 : SABMap tK t₀ x)
    (w1 : LB.Iso tK.PP.L (t₀.PP.L.pull m1.φ)), RigIso m1 w1 →
    ∀ (N : ℕ) (ok : (Over.mk x ⟶ t₀.G) → Prop) (s : LB.Sec (LPow t₀.G t₀.PP.L 1 (Over.mk x)))
      (tt : Over.mk x ⟶ t₀.G) (F : LB.Sec (LPow t₀.G t₀.PP.L ((N : ℤ) ^ 2) (Over.mk x))),
      IsVtOver t₀.G t₀.PP N ok s tt F → (∀ u, ok u → u ^ (N ^ 2) = 1) →
    ∀ sK : LB.Sec (LPow tK.G tK.PP.L ((1 : ℕ) : ℤ) (𝟙_ (Over (Sp K)))),
      TieMv m1 w1 1 (zCast t₀.G Nat.cast_one.symm s) sK →
      ∃ (ttK : 𝟙_ (Over (Sp K)) ⟶ tK.G) (FK : LB.Sec (LPow tK.G tK.PP.L ((N : ℤ) ^ 2) (𝟙_ (Over (Sp K))))),
        IsVtOver tK.G tK.PP N (fun u => u ^ (N ^ 2) = 1) (zCast tK.G Nat.cast_one sK) ttK FK ∧
        TieMv m1 w1 (N ^ 2) (zCast t₀.G (natCast_sq N) F) (zCast tK.G (natCast_sq N) FK)

def ThetaTieSt : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l)
    (c : Coeff l) (Tc : CDVR) (io : c.F →+* Tc.Fr) (y : letI := io.toAlgebra; FrPt Xo c Tc.Fr)
    (I : IntData Xo c Tc io y),
    letI := io.toAlgebra
    ∃ θ : LB.Sec (LB.LinComb I.G.PP.L (K := Fin 1) (fun _ => 𝟙 I.G.G.left) (fun _ => ((1 : ℕ) : ℤ))),
      (∀ σ : LB.Sec (LB.LinComb I.G.PP.L (K := Fin 1) (fun _ => 𝟙 I.G.G.left) (fun _ => ((1 : ℕ) : ℤ))),
        ∃! a : Tc.V, ∀ i, σ.f i = resG I.G.G.left le_top ((I.G.G.hom).appTop.hom (toΓ Tc.V a)) * θ.f i) ∧
      ∃ θK : LB.Sec (LPow I.t'.G I.t'.PP.L ((1 : ℕ) : ℤ) (𝟙_ (Over (Sp Tc.Fr)))),
        TieMv I.m1 I.w1 1 (zCast Xo.univ.t.G Nat.cast_one.symm y.s) θK ∧ SecTieK I.m2 I.w2 1 θK θ

section Restrict

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {S : Scheme.{0}}

def gsec (G : Over S) : G.left ⟶ (𝟙_ (Over S) ⊗ G).left := (lift (toUnit G) (𝟙 G)).left

theorem gsec_snd (G : Over S) : gsec G ≫ (snd (𝟙_ (Over S)) G).left = 𝟙 _ := by
  rw [gsec, ← Over.comp_left, lift_snd, Over.id_left]

theorem exists_restrict (t : SAB H S) (a : ℤ) (F : LB.Sec (LPow t.G t.PP.L a (𝟙_ (Over S)))) :
    ∃ σ : LB.Sec (LB.LinComb t.PP.L (K := Fin 1) (fun _ => 𝟙 t.G.left) (fun _ => a)),
      ∀ (Z : Scheme.{0}) (r : Z ⟶ t.G.left) (z : Z) (J : (Z ⟶ t.G.left) → t.PP.L.ι), Good t.PP.L z J →
        sval σ r z J = sval F (r ≫ gsec t.G) z J := by
  have hF : FormEq (Sum.elim (fun k => gsec t.G ≫ (fun _ : Fin 1 => (snd (𝟙_ (Over S)) t.G).left) k)
      (PEmpty.elim : PEmpty → _)) (Sum.elim (fun _ : Fin 1 => a) (PEmpty.elim : PEmpty → ℤ))
      (fun _ : Fin 1 => 𝟙 t.G.left) (fun _ => a) := by
    intro U _ h
    have e := gsec_snd t.G
    simp only [Fintype.prod_sum_type, Sum.elim_inl, e, Finset.univ_eq_empty, Finset.prod_empty, _root_.mul_one]
  obtain ⟨σ, hσ⟩ := exists_sec t.PP.isLB hF
    (pullMulSec (F : LB.Sec (LB.LinComb t.PP.L (fun _ : Fin 1 => (snd (𝟙_ (Over S)) t.G).left) (fun _ => a)))
      (gsec t.G) (LB.oneGen t.PP.L) (fun _ _ => by dsimp only [LB.oneGen]; erw [map_one, map_one, _root_.mul_one]; simp [LB.LinComb]; rfl))
  refine ⟨σ, fun Z r z J hJ => ?_⟩
  refine (hσ Z r z J hJ).trans ((sval_pullMulSec _ _ _ _ r z hJ).trans ?_)
  rw [val_one, Units.val_one, _root_.mul_one]

end Restrict

theorem isUnit_natCast_of_overLa {K : Type} [Field K] [NumberField K] {la : HeightOneSpectrum (𝓞 K)} (Tc : CDVR)
    {io : K →+* Tc.Fr} {e : ℕ} (ho : OverLa la Tc.V io e) {M : ℕ} (hM : (M : 𝓞 K) ∉ la.asIdeal) :
    IsUnit (M : Tc.V) := by
  have h1 : la.valuation K (M : K) = 1 := by
    have e1 : (M : K) = algebraMap (𝓞 K) K (M : 𝓞 K) := by simp
    rw [e1, HeightOneSpectrum.valuation_of_algebraMap, HeightOneSpectrum.intValuation_eq_one_iff]
    exact hM
  have h2 := ho.2 (M : K)
  rw [vLa, h1, WithZero.log_one, neg_zero, mul_zero, map_natCast] at h2
  have e2 : ((M : ℕ) : Tc.Fr) = algebraMap Tc.V Tc.Fr (M : Tc.V) := by simp
  rw [e2, vV, valV, HeightOneSpectrum.valuation_of_algebraMap, neg_eq_zero] at h2
  have hne : (IsDiscreteValuationRing.maximalIdeal Tc.V).intValuation (M : Tc.V) ≠ 0 := by
    refine HeightOneSpectrum.intValuation_ne_zero _ _ ?_
    intro h0
    apply hM
    have : M = 0 := by exact_mod_cast h0
    rw [this, Nat.cast_zero]; exact la.asIdeal.zero_mem
  have h3 : (IsDiscreteValuationRing.maximalIdeal Tc.V).intValuation (M : Tc.V) = 1 := by
    rw [← WithZero.exp_log hne, h2, WithZero.exp_zero]
  rw [HeightOneSpectrum.intValuation_eq_one_iff] at h3
  by_contra hu
  exact h3 ((IsLocalRing.mem_maximalIdeal _).2 hu)

end ReciprocityTheory.ChartRestriction.G.PullbackSections
