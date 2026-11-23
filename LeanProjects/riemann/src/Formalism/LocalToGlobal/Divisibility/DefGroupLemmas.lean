import Formalism.LocalToGlobal.Divisibility.DefGroup
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.LevelSubgroupFiniteAdelicStandard
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Stabstd
import Formalism.SatakeDualWeyl.KpqSubgroupCompact
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.CsSpan
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.CsApprox
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.CsEasy
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.CsEquiv
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Stdform
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.CsScale
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.CsDual
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.CsGlob
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Afsplit
import Formalism.LocalRingCardinality.MinkMEqMinkowskiNumber

noncomputable section

namespace Formalism.L2.DIV

open NumberField IsDedekindDomain Matrix Formalism.UG Formalism.BasicNotions Formalism.L2.Herm
open scoped TensorProduct

def IsConjPl {E : Type} [Field E] [NumberField E] [StarRing E] (PP PP' : Pl E) : Prop :=
  ∀ a b : 𝓞 E, (b : E) = star (a : E) → (a ∈ PP.asIdeal ↔ b ∈ PP'.asIdeal)

def IsSplitSet {E : Type} [Field E] [NumberField E] [StarRing E] (T : Finset (Pl E)) : Prop :=
  ∀ PP ∈ T, ∀ PP' ∈ T, ¬ IsConjPl PP PP'

def FrameExists : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (n : ℕ)
    (L : Submodule (𝓞 E) (Fin n → E)), Submodule.IsLattice E L →
    ∃ β : GL (Fin n) (E ⊗[F] Af F), IsFrame β L

def FrameStd : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (n : ℕ),
    IsFrame (1 : GL (Fin n) (E ⊗[F] Af F)) (stdLat (n := Fin n) (A := E) (𝓞 E))

def StdSpaceLat : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [StarRing E] (n : ℕ) (neg : Bool),
    crdLat (stdSpace (E := E) n neg) (stdSpace (E := E) n neg).L0 = stdLat (n := Fin n) (A := E) (𝓞 E)

def StEqStab : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (n : ℕ)
    (L : Submodule (𝓞 E) (Fin n → E)) (β : GL (Fin n) (E ⊗[F] Af F)), IsFrame β L →
    St β = stabGL (hatL (F := F) L)

def BaseEqLevelAfL : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] (hc : CMData F E)
    (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (L : Submodule (𝓞 E) (Fin n → E)) (β : GL (Fin n) (E ⊗[F] Af F)),
    IsFrame β L → UA hc J ⊓ St β = levelAfL hc.sig J L

def FrameChange : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (n : ℕ)
    (L : Submodule (𝓞 E) (Fin n → E)) (β β' : GL (Fin n) (E ⊗[F] Af F)), IsFrame β L → IsFrame β' L →
    ∃ u : GL (Fin n) (intAf F E), β' = β * intGL F E n u ∧ St β' = St β ∧
      ∀ (PP : Pl E), ∀ x ∈ St β, redFn β' PP x = (bc (resS F PP) u)⁻¹ * redFn β PP x * bc (resS F PP) u

def RedLocal : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (n : ℕ)
    (β : GL (Fin n) (E ⊗[F] Af F)) (PP : Pl E) (v : HeightOneSpectrum (𝓞 F)),
    v.asIdeal = PP.asIdeal.comap (algebraMap (𝓞 F) (𝓞 E)) →
    ∀ x ∈ St β, bc (prV (E := E) v) x = 1 → redFn β PP x = 1

def RedSurj : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] (hc : CMData F E)
    (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (L : Submodule (𝓞 E) (Fin n → E)) (β : GL (Fin n) (E ⊗[F] Af F))
    (T : Finset (Pl E)), IsDefUnimod hc J L → IsFrame β L → IsSplitSet T →
    ∀ y : ∀ PP : ↥T, GL (Fin n) (kP PP.1), ∃ x ∈ UA hc J ⊓ St β, ∀ PP : ↥T, redFn β PP.1 x = y PP

def RHomSurj : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] (hc : CMData F E)
    (LL : Type) [CommRing LL] (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (L : Submodule (𝓞 E) (Fin n → E))
    (β : GL (Fin n) (E ⊗[F] Af F)) (D : LevDat E LL n) (T : Finset (Pl E)),
    IsDefUnimod hc J L → IsFrame β L → D.Pg ⊆ T → D.Q ⊆ T → IsSplitSet T → Disjoint D.Pg D.Q →
    Function.Surjective (rHom hc J β D)

def KgConj : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] (hc : CMData F E)
    (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (L : Submodule (𝓞 E) (Fin n → E)) (β : GL (Fin n) (E ⊗[F] Af F))
    (PP PP' : Pl E), IsDefUnimod hc J L → IsFrame β L → IsConjPl PP PP' →
    ∀ x ∈ UA hc J, x ∈ princAt β PP → x ∈ princAt β PP'

def KgInPrinc : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] (hc : CMData F E)
    (S : HSpace E) (L : Submodule (𝓞 E) (Fin S.rank → E)) (β : GL (Fin S.rank) (E ⊗[F] Af F))
    (gp : Fin 2 → ℕ) (pb : Fin 2 → 𝓞 E), IsDefUnimod hc S.gram L → IsFrame β L → IsTypeDatum gp pb →
    ∀ x : GL (Fin S.rank) (E ⊗[F] Af F), x ∈ Kg hc S.gram β (primesOf (pb 0 * pb 1)) ↔
      x ∈ levelAfL hc.sig S.gram L ∧ ∀ (i : Fin 2) (v : HeightOneSpectrum (𝓞 F)), (gp i : 𝓞 F) ∈ v.asIdeal →
        InPrinc hc S v (gp i) L (bc (prV (E := E) v) x)

def KgFiniteIndex : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] (hc : CMData F E)
    (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (β : GL (Fin n) (E ⊗[F] Af F)) (T : Finset (Pl E)),
    (Kg hc J β T).relIndex (UA hc J ⊓ St β) ≠ 0

def LevFiniteIndex : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] (hc : CMData F E)
    (LL : Type) [CommRing LL] (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (L : Submodule (𝓞 E) (Fin n → E))
    (β : GL (Fin n) (E ⊗[F] Af F)) (D : LevDat E LL n), IsFrame β L →
    lev hc J β D ≤ levelAfL hc.sig J L ∧ (lev hc J β D).relIndex (levelAfL hc.sig J L) ≠ 0

def ClassSetFiniteOfIndex : Prop :=
  ∀ (G : Type) [Group G] (Γ K K' : Subgroup G), K' ≤ K → K'.relIndex K ≠ 0 →
    Finite (ClassSet Γ K) → Finite (ClassSet Γ K')

def ClFinite : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] (hc : CMData F E)
    (LL : Type) [CommRing LL] (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (L : Submodule (𝓞 E) (Fin n → E))
    (β : GL (Fin n) (E ⊗[F] Af F)) (D : LevDat E LL n), IsDefUnimod hc J L → IsFrame β L →
    Finite (Cl hc J (lev hc J β D))

def GamFinite : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] (hc : CMData F E)
    (LL : Type) [CommRing LL] (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (L : Submodule (𝓞 E) (Fin n → E))
    (β : GL (Fin n) (E ⊗[F] Af F)) (D : LevDat E LL n), IsDefUnimod hc J L → IsFrame β L →
    ∀ c : Cl hc J (lev hc J β D), Finite (Gam c)

def GamMinkowski : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] (hc : CMData F E)
    (LL : Type) [CommRing LL] (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (L : Submodule (𝓞 E) (Fin n → E))
    (β : GL (Fin n) (E ⊗[F] Af F)) (D : LevDat E LL n), IsDefUnimod hc J L → IsFrame β L →
    ∀ c : Cl hc J (lev hc J β D), Nat.card (Gam c) ∣ minkNum (Module.finrank ℚ E * n)

def GamCardStabAt : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] (hc : CMData F E)
    (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (K : Subgroup (GL (Fin n) (E ⊗[F] Af F))) (c : Cl hc J K),
    Nat.card (Gam c) = Nat.card (stabAt (UQ hc J) (K.subgroupOf (UA hc J)) (rep c))

def LatAtUnimod : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] (hc : CMData F E)
    (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (L : Submodule (𝓞 E) (Fin n → E))
    (K : Subgroup (GL (Fin n) (E ⊗[F] Af F))), IsDefUnimod hc J L → ∀ c : Cl hc J K, IsDefUnimod hc J (latAt L c)

def LatAtHat : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] (hc : CMData F E)
    (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (L : Submodule (𝓞 E) (Fin n → E))
    (K : Subgroup (GL (Fin n) (E ⊗[F] Af F))), Submodule.IsLattice E L → ∀ c : Cl hc J K,
    Carries ((rep c : UA hc J) : GL (Fin n) (E ⊗[F] Af F)) L (latAt L c)

def GamStabLat : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] (hc : CMData F E)
    (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (L : Submodule (𝓞 E) (Fin n → E))
    (K : Subgroup (GL (Fin n) (E ⊗[F] Af F))), K ≤ stabGL (hatL (F := F) L) → ∀ c : Cl hc J K,
    ∀ γ ∈ Gam c, (γ : GL (Fin n) E) ∈ stabGL (latAt L c)

def StdIsDefUnimod : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] (hc : CMData F E)
    (n : ℕ) (neg : Bool),
    IsDefUnimod hc (stdSpace (E := E) n neg).gram (stdLat (n := Fin n) (A := E) (𝓞 E))

section Proved

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] {n : ℕ}
  {LL : Type} [CommRing LL]

instance (PP : Pl E) : Finite (kP PP) := Ideal.finiteQuotientOfFreeOfNeBot PP.asIdeal PP.ne_bot

theorem finite_residue_group (Pg : Finset (Pl E)) (r : ℕ) : Finite (G0 Pg r) := by
  have : ∀ PP : ↥Pg, Finite (GL (Fin r) (kP PP.1)) := fun PP => inferInstance
  infer_instance

theorem mem_lev_of_bot {hc : CMData F E} {J : Matrix (Fin n) (Fin n) E} {β : GL (Fin n) (E ⊗[F] Af F)}
    {D : LevDat E LL n} (hD : D.P.H = ⊥) (x : GL (Fin n) (E ⊗[F] Af F)) :
    x ∈ lev hc J β D ↔ ∃ h : x ∈ parLev hc J β D, (⟨x, h⟩ : parLev hc J β D) ∈ (rHom hc J β D).ker := by
  constructor
  · rintro ⟨h1, h2⟩
    rw [hD] at h2
    exact ⟨h1, h2⟩
  · rintro ⟨h1, h2⟩
    refine ⟨h1, ?_⟩
    rw [hD]
    exact h2

theorem lev_of_top {hc : CMData F E} {J : Matrix (Fin n) (Fin n) E} {β : GL (Fin n) (E ⊗[F] Af F)}
    {D : LevDat E LL n} (hD : D.P.H = ⊤) : lev hc J β D = parLev hc J β D := by
  ext x
  constructor
  · exact fun h => h.1
  · intro h
    refine ⟨h, ?_⟩
    rw [hD]; exact Subgroup.mem_top _

end Proved

theorem mem_stdLatS {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}
    (z : Fin n → E ⊗[F] Af F) :
    z ∈ stdLat (n := Fin n) (A := E ⊗[F] Af F) ↥(intAf F E) ↔ ∀ i, z i ∈ intAf F E := by
  constructor
  · intro h i
    obtain ⟨s, hs⟩ := h i (Set.mem_univ i)
    rw [← hs]; exact s.2
  · intro h i _
    exact ⟨⟨z i, h i⟩, rfl⟩

theorem frame_standard : FrameStd := by
  intro F E _ _ _ _ _ n x
  unfold hatL
  rw [Formalism.UG.P.easyc_latS_std, mem_stdLatS]
  simp only [inv_one, Units.val_one, Matrix.one_mulVec]

theorem stabilizer_eq_stabilizer_lattice : StEqStab := by
  intro F E _ _ _ _ _ n L β hβ
  have hstd : stabGL (stdLat (n := Fin n) (A := E ⊗[F] Af F) ↥(intAf F E)) = (intGL F E n).range :=
    Formalism.UG.P.stabilizer_standard_lattice (E ⊗[F] Af F) ↥(intAf F E) (Fin n) Subtype.val_injective
  have hβ' : ∀ x : Fin n → E ⊗[F] Af F, x ∈ hatL (F := F) L ↔
      ((β⁻¹ : GL (Fin n) (E ⊗[F] Af F)) : Matrix (Fin n) (Fin n) (E ⊗[F] Af F)) *ᵥ x ∈
        stdLat (n := Fin n) (A := E ⊗[F] Af F) ↥(intAf F E) := by
    intro x; rw [mem_stdLatS]; exact hβ x
  have key : ∀ g : GL (Fin n) (E ⊗[F] Af F), g ∈ stabGL (hatL (F := F) L) ↔
      β⁻¹ * g * β ∈ stabGL (stdLat (n := Fin n) (A := E ⊗[F] Af F) ↥(intAf F E)) := by
    intro g
    constructor
    · intro hg z
      have h1 := hβ' ((β : Matrix (Fin n) (Fin n) (E ⊗[F] Af F)) *ᵥ z)
      have h2 := hβ' ((g : Matrix (Fin n) (Fin n) (E ⊗[F] Af F)) *ᵥ
        ((β : Matrix (Fin n) (Fin n) (E ⊗[F] Af F)) *ᵥ z))
      have h3 := hg ((β : Matrix (Fin n) (Fin n) (E ⊗[F] Af F)) *ᵥ z)
      rw [Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec] at h1
      have e : ((β⁻¹ : GL (Fin n) (E ⊗[F] Af F)) : Matrix (Fin n) (Fin n) (E ⊗[F] Af F)) *ᵥ
          ((g : Matrix (Fin n) (Fin n) (E ⊗[F] Af F)) *ᵥ ((β : Matrix (Fin n) (Fin n) (E ⊗[F] Af F)) *ᵥ z)) =
          (((β⁻¹ : GL (Fin n) (E ⊗[F] Af F)) : Matrix (Fin n) (Fin n) (E ⊗[F] Af F)) *
            (g : Matrix (Fin n) (Fin n) (E ⊗[F] Af F)) * (β : Matrix (Fin n) (Fin n) (E ⊗[F] Af F))) *ᵥ z := by
        rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Matrix.mul_assoc]
      rw [e] at h2
      rw [Units.val_mul, Units.val_mul]
      exact h1.symm.trans (h3.trans h2)
    · intro hg x
      have h1 := hβ' x
      have h2 := hβ' ((g : Matrix (Fin n) (Fin n) (E ⊗[F] Af F)) *ᵥ x)
      have h3 := hg (((β⁻¹ : GL (Fin n) (E ⊗[F] Af F)) : Matrix (Fin n) (Fin n) (E ⊗[F] Af F)) *ᵥ x)
      rw [Units.val_mul, Units.val_mul, Matrix.mulVec_mulVec, Matrix.mul_assoc, Units.mul_inv, Matrix.mul_one,
        ← Matrix.mulVec_mulVec] at h3
      exact h1.trans (h3.trans h2.symm)
  ext g
  rw [key, hstd]
  constructor
  · rintro ⟨y, rfl⟩
    refine ⟨y, ?_⟩
    simp [frGL, mul_assoc]
  · rintro ⟨y, hy⟩
    refine ⟨y, ?_⟩
    simp only [frGL, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    rw [hy]; group

theorem base_level_eq_adelic_level : BaseEqLevelAfL := by
  intro F E _ _ _ _ _ _ hc n J L β hβ
  rw [stabilizer_eq_stabilizer_lattice F E n L β hβ]
  rfl

def redT {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]
    (hc : CMData F E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (β : GL (Fin n) (E ⊗[F] Af F)) (T : Finset (Pl E)) :
    ↥(UA hc J ⊓ St β) →* (∀ PP : ↥T, GL (Fin n) (kP PP.1)) :=
  MonoidHom.pi fun PP => (redAt β PP.1).comp (Subgroup.inclusion inf_le_right)

theorem level_finite_index : KgFiniteIndex := by
  intro F E _ _ _ _ _ _ hc n J β T
  have hfin : Finite (∀ PP : ↥T, GL (Fin n) (kP PP.1)) := by
    have : ∀ PP : ↥T, Finite (GL (Fin n) (kP PP.1)) := fun PP => inferInstance
    infer_instance
  have hker : (Kg hc J β T).subgroupOf (UA hc J ⊓ St β) = (redT hc J β T).ker := by
    ext x
    rw [Subgroup.mem_subgroupOf, MonoidHom.mem_ker]
    constructor
    · intro hx
      have h1 : (x : GL (Fin n) (E ⊗[F] Af F)) ∈ ⨅ PP ∈ T, princAt β PP := hx.2
      funext PP
      have h2 := (mem_princAt.1 (Subgroup.mem_iInf.1 (Subgroup.mem_iInf.1 h1 PP.1) PP.2)).2
      unfold redFn at h2
      rw [extendOne_of_mem _ x.2.2] at h2
      exact h2
    · intro hx
      refine ⟨x.2, Subgroup.mem_iInf.2 fun PP => Subgroup.mem_iInf.2 fun hP => mem_princAt.2 ⟨x.2.2, ?_⟩⟩
      unfold redFn
      rw [extendOne_of_mem _ x.2.2]
      exact congrFun hx ⟨PP, hP⟩
  unfold Subgroup.relIndex
  rw [hker]
  have : Finite (↥(UA hc J ⊓ St β) ⧸ (redT hc J β T).ker) :=
    Finite.of_equiv _ (QuotientGroup.quotientKerEquivRange (redT hc J β T)).toEquiv.symm
  exact Subgroup.index_ne_zero_of_finite

theorem level_subgroup_finite_index : LevFiniteIndex := by
  classical
  intro F E _ _ _ _ _ _ hc LL _ n J L β D hβ
  have hb := base_level_eq_adelic_level F E hc n J L β hβ
  have hle : lev hc J β D ≤ levelAfL hc.sig J L := by
    rw [← hb]
    exact fun x hx => ⟨parLev_UA hx.1, parLev_St hx.1⟩
  refine ⟨hle, ?_⟩
  rw [← hb]
  have h1 := level_finite_index F E hc n J β (D.Pg ∪ D.Q)
  have h2 : Kg hc J β (D.Pg ∪ D.Q) ≤ lev hc J β D :=
    Kg_le_lev Finset.subset_union_left Finset.subset_union_right
  exact fun h0 => h1 (Nat.eq_zero_of_zero_dvd (h0 ▸ Subgroup.relIndex_dvd_of_le_left (UA hc J ⊓ St β) h2))

theorem class_set_finite_of_finite_index : ClassSetFiniteOfIndex := by
  intro G _ Γ K K' hle hidx hfin
  have hq : Finite (K ⧸ K'.subgroupOf K) := by
    have : (K'.subgroupOf K).FiniteIndex := ⟨hidx⟩
    infer_instance
  let f : ClassSet Γ K × (K ⧸ K'.subgroupOf K) → ClassSet Γ K' :=
    fun p => DoubleCoset.mk Γ K' (Quotient.out p.1 * ((Quotient.out p.2 : K) : G))
  refine Finite.of_surjective f ?_
  intro c
  rw [← DoubleCoset.out_eq' Γ K' c]
  set g : G := Quotient.out c with hg
  obtain ⟨h, k, hh, hk, e⟩ := DoubleCoset.mk_out_eq_mul Γ K g
  obtain ⟨k', e'⟩ := QuotientGroup.mk_out_eq_mul (K'.subgroupOf K) (⟨k, hk⟩⁻¹ : K)
  refine ⟨(DoubleCoset.mk Γ K g, QuotientGroup.mk (⟨k, hk⟩⁻¹ : K)), ?_⟩
  show DoubleCoset.mk Γ K' (Quotient.out (DoubleCoset.mk Γ K g) *
    ((Quotient.out (QuotientGroup.mk (⟨k, hk⟩⁻¹ : K) : K ⧸ K'.subgroupOf K) : K) : G)) = DoubleCoset.mk Γ K' g
  rw [e, e']
  symm
  rw [DoubleCoset.eq]
  refine ⟨h, hh, ((k' : K) : G), Subgroup.mem_subgroupOf.1 k'.2, ?_⟩
  simp [mul_assoc]

theorem cm_comp {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]
    (hc : CMData F E) (τ : E →+* ℂ) : τ.comp (hc.sig : E →+* E) = (starRingEnd ℂ).comp τ := by
  ext a
  exact hc.cmUnram.2.1 τ a

theorem levelAfL_le_UA {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]
    (hc : CMData F E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (L : Submodule (𝓞 E) (Fin n → E)) :
    levelAfL hc.sig J L ≤ UA hc J := inf_le_left

theorem clFinite_of (h : LevFiniteIndex) : ClFinite := by
  intro F E _ _ _ _ _ _ hc LL _ n J L β D hU hβ
  obtain ⟨hle, hidx⟩ := h F E hc LL n J L β D hβ
  have hfin := Formalism.UG.Final.ClassSetFiniteL F E (Fin n) hc.sig J (cm_comp hc) hU.herm hU.unit hU.tdef L
    (Module.Finite.iff_fg.2 hU.lat.fg) hU.lat.span_eq_top
  refine class_set_finite_of_finite_index _ _ _ _ ?_ ?_ hfin
  · intro x hx
    exact Subgroup.mem_subgroupOf.2 (hle (Subgroup.mem_subgroupOf.1 hx))
  · rw [Subgroup.relIndex_subgroupOf (levelAfL_le_UA hc J L)]
    exact hidx

section GamMap

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] {n : ℕ}

theorem af_nontrivial (F : Type) [Field F] [NumberField F] : Nontrivial (Af F) := by
  obtain ⟨p, hp0, hp⟩ := Ring.not_isField_iff_exists_prime.1 (RingOfIntegers.not_isField F)
  let v : HeightOneSpectrum (𝓞 F) := ⟨p, hp, hp0⟩
  exact (evalV F v).toRingHom.domain_nontrivial

theorem incl_inj (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (n : ℕ) :
    Function.Injective (bc (n := Fin n) (inclE (F := F) (E := E) (Af F))) :=
  Formalism.UG.Final.InclInj F E (Fin n) (Af F) (af_nontrivial F)

variable {hc : CMData F E} {J : Matrix (Fin n) (Fin n) E} {K : Subgroup (GL (Fin n) (E ⊗[F] Af F))}

theorem rat_mem (γ : UR hc J) : bc (inclE (F := F) (Af F)) (γ : GL (Fin n) E) ∈ ratPts hc.sig J (Af F) :=
  ⟨γ.1, γ.2, rfl⟩

def ratEl (γ : UR hc J) : UQ hc J :=
  ⟨⟨bc (inclE (F := F) (Af F)) (γ : GL (Fin n) E), Formalism.UG.Final.RatPtsLe F E (Fin n) hc.sig J (Af F) (rat_mem γ)⟩,
    Subgroup.mem_subgroupOf.2 (rat_mem γ)⟩

theorem ratEl_mem_stabAt (y : UA hc J) (γ : UR hc J) :
    ratEl γ ∈ stabAt (UQ hc J) (K.subgroupOf (UA hc J)) y ↔ conjIn hc J (y : GL (Fin n) (E ⊗[F] Af F)) γ ∈ K := by
  rw [conjIn_apply]
  exact Subgroup.mem_subgroupOf

theorem ratEl_injective : Function.Injective (ratEl (hc := hc) (J := J)) := by
  intro a b h
  have h1 : bc (inclE (F := F) (Af F)) (a : GL (Fin n) E) = bc (inclE (F := F) (Af F)) (b : GL (Fin n) E) :=
    congrArg (fun z : UQ hc J => ((z : UA hc J) : GL (Fin n) (E ⊗[F] Af F))) h
  exact Subtype.ext (incl_inj F E n h1)

theorem ratEl_surjective : Function.Surjective (ratEl (hc := hc) (J := J)) := by
  intro δ
  obtain ⟨γ, hγ, e⟩ := Subgroup.mem_subgroupOf.1 δ.2
  exact ⟨⟨γ, hγ⟩, Subtype.ext (Subtype.ext e)⟩

def gamMap (c : Cl hc J K) (γ : Gam c) : stabAt (UQ hc J) (K.subgroupOf (UA hc J)) (rep c) :=
  ⟨ratEl γ.1, (ratEl_mem_stabAt (rep c) γ.1).2 γ.2⟩

theorem gamMap_bijective (c : Cl hc J K) : Function.Bijective (gamMap c) := by
  constructor
  · intro a b h
    exact Subtype.ext (ratEl_injective (congrArg Subtype.val h))
  · intro δ
    obtain ⟨γ, e⟩ := ratEl_surjective δ.1
    refine ⟨⟨γ, ?_⟩, Subtype.ext e⟩
    have := δ.2
    rw [← e] at this
    exact (ratEl_mem_stabAt (rep c) γ).1 this

end GamMap

theorem gamma_card_stabilizer_at : GamCardStabAt := by
  intro F E _ _ _ _ _ _ hc n J K c
  exact Nat.card_congr (Equiv.ofBijective _ (gamMap_bijective c))

theorem gamFinite_of (h : LevFiniteIndex) : GamFinite := by
  intro F E _ _ _ _ _ _ hc LL _ n J L β D hU hβ c
  obtain ⟨hle, -⟩ := h F E hc LL n J L β D hβ
  have hfin := Formalism.UG.Final.AdelicStabFiniteL F E (Fin n) hc.sig J (cm_comp hc) hU.herm hU.unit hU.tdef L
    (Module.Finite.iff_fg.2 hU.lat.fg) hU.lat.span_eq_top (rep c)
  let f : Gam c → stabAt (UQ hc J) ((levelAfL hc.sig J L).subgroupOf (UA hc J)) (rep c) :=
    fun γ => ⟨ratEl γ.1, (ratEl_mem_stabAt (rep c) γ.1).2 (hle γ.2)⟩
  refine Finite.of_injective f ?_
  intro a b hab
  exact Subtype.ext (ratEl_injective (congrArg Subtype.val hab))

theorem lattice_completion_at : LatAtHat := by
  intro F E _ _ _ _ _ _ hc n J L K hL c x
  exact Formalism.UG.P.span_recovery_of_integral_adelic_approx Formalism.UG.P.integral_adele_approximation_holds F E (Fin n) L (Module.Finite.iff_fg.2 hL.fg)
    hL.span_eq_top ((rep c : UA hc J) : GL (Fin n) (E ⊗[F] Af F)) x

theorem class_set_finite : ClFinite := clFinite_of level_subgroup_finite_index

theorem stabilizers_finite : GamFinite := gamFinite_of level_subgroup_finite_index

theorem hform_diagonal {E : Type} [Field E] {n : ℕ} (σ : E →+* E) (d : Fin n → E) (x y : Fin n → E) :
    hform σ (Matrix.diagonal d) x y = ∑ i, σ (x i) * d i * y i := by
  unfold hform
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_eq_single i]
  · rw [Matrix.diagonal_apply_eq]
  · intro j _ hj
    rw [Matrix.diagonal_apply_ne _ (Ne.symm hj), mul_zero, zero_mul]
  · intro h; exact absurd (Finset.mem_univ i) h

theorem sgn_mem_range {E : Type} [Field E] [NumberField E] (b : Bool) :
    (Formalism.BasicNotions.Examples₂.sgn b : E) ∈ (algebraMap (𝓞 E) E).range :=
  ⟨Formalism.BasicNotions.Examples₂.sgn b, Formalism.BasicNotions.Examples₂.map_sgn _ b⟩

theorem standard_definite_unimodular : StdIsDefUnimod := by
  intro F E _ _ _ _ _ _ hc n neg
  have hstd := Formalism.UG.P.standard_hermitian_form_definite F E (Fin n) hc.sig (cm_comp hc)
    (fun e he => (hc.fixed e).1 he) hc.totReal
  have hg : (stdSpace (E := E) n neg).gram = Matrix.diagonal (fun _ => (Formalism.BasicNotions.Examples₂.sgn neg : E)) :=
    stdSpace_gram n neg
  have hfull := Formalism.UG.P.standard_lattice_full_holds E (Fin n)
  have hJ : (Matrix.diagonal (fun _ : Fin n => (Formalism.BasicNotions.Examples₂.sgn neg : E)) = 1 ∧ neg = false) ∨
      (Matrix.diagonal (fun _ : Fin n => (Formalism.BasicNotions.Examples₂.sgn neg : E)) = -1 ∧ neg = true) := by
    cases neg
    · left; exact ⟨by simp [Formalism.BasicNotions.Examples₂.sgn], rfl⟩
    · right
      refine ⟨?_, rfl⟩
      ext i j
      by_cases h : i = j
      · subst h; simp [Formalism.BasicNotions.Examples₂.sgn]
      · simp [Formalism.BasicNotions.Examples₂.sgn, h]
  have key : IsDefUnimod hc (Matrix.diagonal (fun _ : Fin n => (Formalism.BasicNotions.Examples₂.sgn neg : E)))
      (stdLat (n := Fin n) (A := E) (𝓞 E)) := by
    refine ⟨?_, ?_, ?_, ⟨Module.Finite.iff_fg.1 hfull.1, hfull.2⟩, ?_⟩
    · rcases hJ with ⟨h, _⟩ | ⟨h, _⟩
      · rw [h]; exact hstd.1
      · rw [h]
        have h1 : cT (hc.sig : E →+* E) (1 : Matrix (Fin n) (Fin n) E) = 1 := hstd.1
        show cT (hc.sig : E →+* E) (-1 : Matrix (Fin n) (Fin n) E) = -1
        unfold cT at h1 ⊢
        rw [show ((-1 : Matrix (Fin n) (Fin n) E).map (hc.sig : E →+* E)) =
          -((1 : Matrix (Fin n) (Fin n) E).map (hc.sig : E →+* E)) by
            ext i j
            show (hc.sig : E →+* E) (-((1 : Matrix (Fin n) (Fin n) E) i j)) =
              -((hc.sig : E →+* E) ((1 : Matrix (Fin n) (Fin n) E) i j))
            rw [map_neg], Matrix.transpose_neg, h1]
    · rw [Matrix.det_diagonal]
      refine IsUnit.mk0 _ (Finset.prod_ne_zero_iff.2 fun i _ => Formalism.BasicNotions.Examples₂.sgn_ne_zero neg)
    · rcases hJ with ⟨h, _⟩ | ⟨h, _⟩
      · rw [h]; exact hstd.2.1
      · rw [h]; exact hstd.2.2
    · ext y
      constructor
      · intro hy
        show y ∈ stdLat (n := Fin n) (A := E) (𝓞 E)
        rw [Formalism.UG.P.mem_stdLat_iff']
        intro i
        have h1 := hy (Pi.single i 1) (Formalism.UG.P.easyc_single_mem i)
        rw [hform_diagonal, Finset.sum_eq_single i] at h1
        · rw [Pi.single_eq_same, map_one, one_mul] at h1
          have h2 := (algebraMap (𝓞 E) E).range.mul_mem (sgn_mem_range (E := E) neg) h1
          rw [← mul_assoc, Formalism.BasicNotions.Examples₂.sgn_mul_self, one_mul] at h2
          exact h2
        · intro j _ hj
          rw [Pi.single_eq_of_ne hj, map_zero, zero_mul, zero_mul]
        · intro h; exact absurd (Finset.mem_univ i) h
      · intro hy x hx
        have hy' := (Formalism.UG.P.mem_stdLat_iff' y).1 hy
        have hx' := (Formalism.UG.P.mem_stdLat_iff' x).1 hx
        rw [hform_diagonal]
        refine Subring.sum_mem _ fun i _ => ?_
        refine Subring.mul_mem _ (Subring.mul_mem _ ?_ (sgn_mem_range neg)) (hy' i)
        obtain ⟨a, ha⟩ := hx' i
        rw [← ha]
        exact Formalism.BasicNotions.Examples₂.star_integral Formalism.BasicNotions.Examples₂.star_isIntegral a
  have e : IsDefUnimod hc (stdSpace (E := E) n neg).gram (stdLat (n := Fin n) (A := E) (𝓞 E)) := by
    rw [hg]; exact key
  exact e

theorem toyStdLat_eq (E : Type) [Field E] [NumberField E] [StarRing E] (n : ℕ) :
    Formalism.BasicNotions.Examples₂.stdLat (E := E) n = stdLat (n := Fin n) (A := E) (𝓞 E) := by
  apply le_antisymm
  · unfold Formalism.BasicNotions.Examples₂.stdLat
    rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    rw [Pi.basisFun_apply]
    exact Formalism.UG.P.easyc_single_mem i
  · intro x hx
    have hx' := (Formalism.UG.P.mem_stdLat_iff' x).1 hx
    choose a ha using hx'
    have : x = ∑ i, a i • (Pi.basisFun E (Fin n)) i := by
      funext j
      rw [Finset.sum_apply, Finset.sum_eq_single j]
      · rw [Pi.smul_apply, Pi.basisFun_apply, Pi.single_eq_same, Algebra.smul_def, mul_one, ha]
      · intro i _ hi
        rw [Pi.smul_apply, Pi.basisFun_apply, Pi.single_eq_of_ne (Ne.symm hi), smul_zero]
      · intro h; exact absurd (Finset.mem_univ j) h
    rw [this]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)

theorem standard_space_lattice : StdSpaceLat := by
  intro E _ _ _ n neg
  have h1 : (crdLat (stdSpace (E := E) n neg) (stdSpace (E := E) n neg).L0 : Submodule (𝓞 E) (Fin n → E)) =
      (Formalism.BasicNotions.Examples₂.stdLat (E := E) n) := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact hy
    · intro hx
      exact ⟨x, hx, rfl⟩
  exact h1.trans (toyStdLat_eq E n)

theorem gamma_stabilizes_lattice : GamStabLat := by
  intro F E _ _ _ _ _ _ hc n J L K hK c γ hγ
  set y : GL (Fin n) (E ⊗[F] Af F) := ((rep c : UA hc J) : GL (Fin n) (E ⊗[F] Af F)) with hy
  have hk : y⁻¹ * bc (inclE (F := F) (Af F)) (γ : GL (Fin n) E) * y ∈ K := by
    have : conjIn hc J y γ ∈ K := hγ
    rwa [conjIn_apply] at this
  have hequiv := Formalism.UG.P.global_lattice_equiv_holds F E (Fin n) L (γ : GL (Fin n) E) y
    ((y⁻¹ * bc (inclE (F := F) (Af F)) (γ : GL (Fin n) E) * y)⁻¹) (Subgroup.inv_mem _ (hK hk))
  have e : bc (inclE (F := F) (Af F)) (γ : GL (Fin n) E) * y *
      (y⁻¹ * bc (inclE (F := F) (Af F)) (γ : GL (Fin n) E) * y)⁻¹ = y := by group
  rw [e] at hequiv
  rw [Formalism.UG.P.stabilizer_group_map_holds E (𝓞 E) (Fin n) (latAt L c) (γ : GL (Fin n) E)]
  exact hequiv.symm

theorem frame_change_bis : FrameChange := by
  intro F E _ _ _ _ _ n L β β' hβ hβ'
  have hstd : stabGL (stdLat (n := Fin n) (A := E ⊗[F] Af F) ↥(intAf F E)) = (intGL F E n).range :=
    Formalism.UG.P.stabilizer_standard_lattice (E ⊗[F] Af F) ↥(intAf F E) (Fin n) Subtype.val_injective
  have hmem : β⁻¹ * β' ∈ stabGL (stdLat (n := Fin n) (A := E ⊗[F] Af F) ↥(intAf F E)) := by
    intro z
    have h1 := hβ' ((β' : Matrix (Fin n) (Fin n) (E ⊗[F] Af F)) *ᵥ z)
    have h2 := hβ ((β' : Matrix (Fin n) (Fin n) (E ⊗[F] Af F)) *ᵥ z)
    rw [Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec] at h1
    rw [Matrix.mulVec_mulVec] at h2
    rw [mem_stdLatS, mem_stdLatS, Units.val_mul]
    exact h1.symm.trans h2
  rw [hstd] at hmem
  obtain ⟨u, hu⟩ := hmem
  have hb : β' = β * intGL F E n u := by rw [hu]; group
  refine ⟨u, hb, ?_, ?_⟩
  · rw [stabilizer_eq_stabilizer_lattice F E n L β hβ, stabilizer_eq_stabilizer_lattice F E n L β' hβ']
  · rintro PP x ⟨y, rfl⟩
    have e : frGL β y = frGL β' (u⁻¹ * y * u) := by
      simp only [frGL, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, map_mul, map_inv]
      rw [hb]; group
    rw [redFn_frGL]
    rw [e, redFn_frGL, map_mul, map_mul, map_inv]

section HatDual

open Formalism.UG.P

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}

local notation "𝒜" => E ⊗[F] FiniteAdeleRing (𝓞 F) F
local notation "𝒮" => tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (intOE E) (intAd F)
local notation "ιA" => inclE (F := F) (E := E) (FiniteAdeleRing (𝓞 F) F)

theorem levelafC_eq_incl (D : 𝓞 F) : levelafC E D = ιA (algebraMap (𝓞 F) E D) := by
  have := csGlob_tmul_int (F := F) (E := E) (1 : E) D
  rw [mul_one] at this
  exact this

theorem latS_approx (L : Submodule (𝓞 E) (Fin n → E)) (D : 𝓞 F) (hD : D ≠ 0) (v : Fin n → 𝒜)
    (hv : v ∈ latS (F := F) (FiniteAdeleRing (𝓞 F) F) 𝒮 L) :
    ∃ l0 ∈ L, ∃ l1 ∈ latS (F := F) (FiniteAdeleRing (𝓞 F) F) 𝒮 L,
      v = (fun i => ιA (l0 i)) + (fun i => levelafC E D * l1 i) := by
  unfold latS at hv
  induction hv using Submodule.span_induction with
  | mem v hv =>
    obtain ⟨l, hl, rfl⟩ := hv
    exact ⟨l, hl, 0, Submodule.zero_mem _, by funext i; simp⟩
  | zero => exact ⟨0, Submodule.zero_mem _, 0, Submodule.zero_mem _, by funext i; simp⟩
  | add u v _ _ hu hv =>
    obtain ⟨a0, ha0, a1, ha1, rfl⟩ := hu
    obtain ⟨b0, hb0, b1, hb1, rfl⟩ := hv
    refine ⟨a0 + b0, Submodule.add_mem _ ha0 hb0, a1 + b1, Submodule.add_mem _ ha1 hb1, ?_⟩
    funext i
    simp only [Pi.add_apply, map_add]
    ring
  | smul s v _ hv =>
    obtain ⟨a0, ha0, a1, ha1, rfl⟩ := hv
    obtain ⟨b, t, ht, hs⟩ := csGlob_approx (F := F) (E := E) csGlob_intAdApprox D hD (s : 𝒜) s.2
    refine ⟨b • a0, Submodule.smul_mem _ _ ha0,
      (⟨t, ht⟩ : 𝒮) • (fun i => ιA (a0 i)) + s • a1,
      Submodule.add_mem _ (Submodule.smul_mem _ _ (Submodule.subset_span ⟨a0, ha0, rfl⟩))
        (Submodule.smul_mem _ _ ha1), ?_⟩
    funext i
    show (s : 𝒜) * (ιA (a0 i) + levelafC E D * a1 i) =
      ιA (b • a0 i) + levelafC E D * (t * ιA (a0 i) + (s : 𝒜) * a1 i)
    rw [Algebra.smul_def, map_mul]
    conv_lhs => rw [mul_add, hs]
    rw [hs]
    ring

theorem hat_selfdual (σ : E →ₐ[F] E) (J : Matrix (Fin n) (Fin n) E) (L : Submodule (𝓞 E) (Fin n → E))
    (hspan : Submodule.span E (L : Set (Fin n → E)) = ⊤)
    (hsd : dualSet (σ : E →+* E) J L = (L : Set (Fin n → E))) (w : Fin n → 𝒜)
    (hw : ∀ l ∈ L, hform (sigR σ (FiniteAdeleRing (𝓞 F) F)) (J.map ιA) (fun i => ιA (l i)) w ∈ 𝒮) :
    w ∈ latS (F := F) (FiniteAdeleRing (𝓞 F) F) 𝒮 L := by
  classical
  have hint : ∀ x ∈ L, ∀ y ∈ L, IsIntegral ℤ (((1 : ℤ) : E) * hform (σ : E →+* E) J x y) := by
    intro x hx y hy
    have hy' : y ∈ dualSet (σ : E →+* E) J L := by rw [hsd]; exact hy
    obtain ⟨a, ha⟩ := hy' x hx
    rw [Int.cast_one, one_mul, ← ha]
    exact RingOfIntegers.isIntegral_coe a
  choose d hd0 hd using fun i => levelaf_denom (E := E) (F := F) (w i)
  obtain ⟨c, hc0, hc⟩ := adelstabL_lower (F := F) L hspan
  set D1 : 𝓞 F := ∏ k, d k with hD1
  have hD1w : ∀ i, levelafC E D1 * w i ∈ 𝒮 := by
    intro i
    rw [hD1, ← Finset.mul_prod_erase _ _ (Finset.mem_univ i), levelafC_mul, mul_comm (levelafC E (d i)), mul_assoc]
    exact mul_mem (levelafC_mem _) (hd i)
  set D : 𝓞 F := c * D1 with hDdef
  have hD0 : D ≠ 0 := mul_ne_zero hc0 (Finset.prod_ne_zero_iff.2 fun i _ => hd0 i)
  have hDw : (fun i => levelafC E D * w i) ∈ latS (F := F) (FiniteAdeleRing (𝓞 F) F) 𝒮 L := by
    have := hc (fun i => levelafC E D1 * w i) hD1w
    simpa only [hDdef, levelafC_mul, mul_assoc] using this
  obtain ⟨l0, hl0, l1, hl1, he⟩ := latS_approx L D hD0 _ hDw
  set δ : E := algebraMap (𝓞 F) E D with hδ
  have hδ0 : δ ≠ 0 := by
    rw [hδ, IsScalarTower.algebraMap_apply (𝓞 F) F E]
    simpa using hD0
  set z0 : Fin n → E := fun i => δ⁻¹ * l0 i with hz0
  have hwi : ∀ i, w i = ιA (z0 i) + l1 i := by
    intro i
    have h1 := congrFun he i
    simp only [Pi.add_apply] at h1
    rw [levelafC_eq_incl] at h1
    have h2 : ιA δ⁻¹ * ιA δ = 1 := by rw [← map_mul, inv_mul_cancel₀ hδ0, map_one]
    calc w i = ιA δ⁻¹ * ιA δ * w i := by rw [h2, one_mul]
      _ = ιA δ⁻¹ * (ιA δ * w i) := by ring
      _ = ιA δ⁻¹ * (ιA (l0 i) + ιA δ * l1 i) := by rw [h1]
      _ = ιA δ⁻¹ * ιA (l0 i) + ιA δ⁻¹ * ιA δ * l1 i := by ring
      _ = ιA (z0 i) + l1 i := by rw [h2, one_mul, hz0, map_mul]
  have hw' : w = (fun i => ιA (z0 i)) + l1 := funext hwi
  have hz0L : z0 ∈ L := by
    have : z0 ∈ dualSet (σ : E →+* E) J L := by
      intro l hl
      have h1 := hw l hl
      rw [hw', csScale_hform_add_right, csScale_hform_incl] at h1
      have h2 := csScale_latS σ J L 1 hint (Submodule.subset_span ⟨l, hl, rfl⟩ :
        (fun i => ιA (l i)) ∈ latS (F := F) (FiniteAdeleRing (𝓞 F) F) 𝒮 L) hl1
      rw [Int.cast_one, map_one, one_mul] at h2
      have h3 : ιA (hform (σ : E →+* E) J l z0) ∈ 𝒮 := by
        have := sub_mem h1 h2
        rwa [add_sub_cancel_right] at this
      have h4 := csGlob_int (F := F) _ h3
      exact ⟨⟨_, h4⟩, rfl⟩
    rw [hsd] at this
    exact this
  rw [hw']
  exact Submodule.add_mem _ (Submodule.subset_span ⟨z0, hz0L, rfl⟩) hl1

end HatDual

theorem lattice_unimodular_at : LatAtUnimod := by
  intro F E _ _ _ _ _ _ hc n J L K hL c
  have hfin : Module.Finite (𝓞 E) L := Module.Finite.iff_fg.2 hL.lat.fg
  have hspan := hL.lat.span_eq_top
  set y : GL (Fin n) (E ⊗[F] Af F) := ((rep c : UA hc J) : GL (Fin n) (E ⊗[F] Af F)) with hy
  have hyU : y ∈ UPts hc.sig J (Af F) := (rep c : UA hc J).2
  have hint : ∀ x ∈ L, ∀ z ∈ L, IsIntegral ℤ (((1 : ℤ) : E) * hform (hc.sig : E →+* E) J x z) := by
    intro x hx z hz
    have hz' : z ∈ dualSet (hc.sig : E →+* E) J L := by rw [hL.selfdual]; exact hz
    obtain ⟨a, ha⟩ := hz' x hx
    rw [Int.cast_one, one_mul, ← ha]
    exact RingOfIntegers.isIntegral_coe a
  refine ⟨hL.herm, hL.unit, hL.tdef, Formalism.UG.P.global_lattice_isLattice_holds F E (Fin n) L hfin hspan y, ?_⟩
  ext z
  constructor
  · intro hz
    show ((y⁻¹ : GL (Fin n) (E ⊗[F] Af F)) : Matrix (Fin n) (Fin n) (E ⊗[F] Af F)) *ᵥ
      (fun i => inclE (F := F) (Af F) (z i)) ∈ latS (F := F) (Af F) (intAf F E) L
    refine hat_selfdual hc.sig J L hspan hL.selfdual _ fun l hl => ?_
    have hg' : cT (sigR hc.sig (Af F)) (y : Matrix (Fin n) (Fin n) (E ⊗[F] Af F)) *
        J.map (inclE (F := F) (Af F)) * (y : Matrix (Fin n) (Fin n) (E ⊗[F] Af F)) =
        J.map (inclE (F := F) (Af F)) := hyU
    have h3 := Formalism.UG.P.hform_mulVec (sigR hc.sig (Af F)) (J.map (inclE (F := F) (Af F)))
      (y : Matrix (Fin n) (Fin n) (E ⊗[F] Af F)) (fun i => inclE (F := F) (Af F) (l i))
      (((y⁻¹ : GL (Fin n) (E ⊗[F] Af F)) : Matrix (Fin n) (Fin n) (E ⊗[F] Af F)) *ᵥ
        (fun i => inclE (F := F) (Af F) (z i)))
    rw [hg', Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec] at h3
    rw [← h3]
    refine Formalism.UG.P.csDual_span hc.sig J (latAt L c) z hz _ ?_
    refine Formalism.UG.P.csSpan_back Formalism.UG.P.integral_adele_approximation_holds L hfin hspan y _ ?_
    rw [Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec]
    exact Submodule.subset_span ⟨l, hl, rfl⟩
  · intro hz x hx
    have h1 := Formalism.UG.P.csScale_glob hc.sig J L 1 hint y hyU hx hz
    have h2 := Formalism.UG.P.csGlob_int (F := F) _ h1
    rw [Int.cast_one, one_mul] at h2
    exact ⟨⟨_, h2⟩, rfl⟩

section ToolA

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

def adS (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] : intAd F →+* intAf F E :=
  (((Algebra.TensorProduct.includeRight : Af F →ₐ[F] E ⊗[F] Af F) : Af F →+* E ⊗[F] Af F).comp
    (intAd F).subtype).codRestrict (intAf F E) (fun a => Subring.subset_closure (Or.inr ⟨a, rfl⟩))

theorem adS_coe (a : intAd F) : ((adS F E a : intAf F E) : E ⊗[F] Af F) = (1 : E) ⊗ₜ[F] (a : Af F) := rfl

def oToAd (F : Type) [Field F] [NumberField F] : 𝓞 F →+* intAd F :=
  (algebraMap (𝓞 F) (Af F)).codRestrict (intAd F) (fun r => Formalism.UG.P.levelaf_int_mem r)

theorem adS_oToAd (r : 𝓞 F) : adS F E (oToAd F r) = oToS F E (algebraMap (𝓞 F) (𝓞 E) r) := by
  apply Subtype.ext
  rw [adS_coe, oToS_coe]
  show (1 : E) ⊗ₜ[F] (algebraMap (𝓞 F) (Af F) r) = _
  rw [Formalism.UG.P.csGlob_tmul_int, mul_one, ← IsScalarTower.algebraMap_apply]
  rfl

theorem resS_eq_zero_iff (PP : Pl E) (s : intAf F E) : resS F PP s = 0 ↔ s ∈ idS F PP.asIdeal := by
  unfold resS
  rw [RingHom.comp_apply]
  show (RingEquiv.ofBijective (cmpS F PP.asIdeal) _).symm _ = 0 ↔ _
  rw [RingEquiv.symm_apply_eq, map_zero, Ideal.Quotient.eq_zero_iff_mem]

theorem resS_adS_eq_zero (PP : Pl E) (v : HeightOneSpectrum (𝓞 F))
    (hv : v.asIdeal = PP.asIdeal.comap (algebraMap (𝓞 F) (𝓞 E))) (a : intAd F)
    (ha : Valued.v ((a : Af F) v) < 1) : resS F PP (adS F E a) = 0 := by
  obtain ⟨D, hDv, hD⟩ := Submodule.exists_mem_ne_zero_of_ne_bot v.ne_bot
  obtain ⟨r, y, hy, e⟩ := Formalism.UG.P.integral_adele_approximation_holds F D hD (a : Af F) a.2
  have hDval : Valued.v (algebraMap (𝓞 F) (v.adicCompletion F) D) < 1 := by
    rw [Formalism.UG.P.csApprox_val_int]
    exact (HeightOneSpectrum.intValuation_lt_one_iff_mem v D).2 hDv
  have hyv : Valued.v (y v) ≤ 1 := (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).1 (hy v)
  have ev : algebraMap (𝓞 F) (v.adicCompletion F) r =
      (a : Af F) v - algebraMap (𝓞 F) (v.adicCompletion F) D * y v := by
    have := congrArg (fun z : Af F => z v) e
    have h2 : (a : Af F) v = algebraMap (𝓞 F) (v.adicCompletion F) r +
        algebraMap (𝓞 F) (v.adicCompletion F) D * y v := this
    rw [h2]; ring
  have hr : r ∈ v.asIdeal := by
    rw [← HeightOneSpectrum.intValuation_lt_one_iff_mem, ← Formalism.UG.P.csApprox_val_int, ev]
    refine lt_of_le_of_lt (Valuation.map_sub _ _ _) (max_lt ha ?_)
    rw [map_mul]
    exact mul_lt_one_of_lt_of_le hDval hyv
  have ea : a = oToAd F r + oToAd F D * ⟨y, hy⟩ := Subtype.ext e
  rw [ea, map_add, map_mul, adS_oToAd, adS_oToAd, map_add, map_mul, resS_oToS, resS_oToS]
  have h1 : Ideal.Quotient.mk PP.asIdeal (algebraMap (𝓞 F) (𝓞 E) r) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.2 (by rw [hv] at hr; exact hr)
  have h2 : Ideal.Quotient.mk PP.asIdeal (algebraMap (𝓞 F) (𝓞 E) D) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.2 (by rw [hv] at hDv; exact hDv)
  rw [h1, h2, zero_mul, add_zero]

def mkAd (f : ∀ v : HeightOneSpectrum (𝓞 F), v.adicCompletion F)
    (h : ∀ v, f v ∈ v.adicCompletionIntegers F) : intAd F :=
  ⟨⟨f, Filter.Eventually.of_forall h⟩, h⟩

theorem mkAd_apply (f : ∀ v : HeightOneSpectrum (𝓞 F), v.adicCompletion F)
    (h : ∀ v, f v ∈ v.adicCompletionIntegers F) (v : HeightOneSpectrum (𝓞 F)) :
    ((mkAd f h : intAd F) : Af F) v = f v := rfl

open Classical in

def idemAd (P : HeightOneSpectrum (𝓞 F) → Prop) : intAd F :=
  mkAd (fun v => if P v then 1 else 0) (fun v => by
    by_cases h : P v
    · simp only [h, if_true]; exact one_mem _
    · simp only [h, if_false]; exact zero_mem _)

theorem idemAd_pos {P : HeightOneSpectrum (𝓞 F) → Prop} {v : HeightOneSpectrum (𝓞 F)} (h : P v) :
    ((idemAd P : intAd F) : Af F) v = 1 := by
  unfold idemAd; rw [mkAd_apply, if_pos h]

theorem idemAd_neg {P : HeightOneSpectrum (𝓞 F) → Prop} {v : HeightOneSpectrum (𝓞 F)} (h : ¬ P v) :
    ((idemAd P : intAd F) : Af F) v = 0 := by
  unfold idemAd; rw [mkAd_apply, if_neg h]

theorem resS_idemAd_neg (PP : Pl E) (v : HeightOneSpectrum (𝓞 F))
    (hv : v.asIdeal = PP.asIdeal.comap (algebraMap (𝓞 F) (𝓞 E))) {P : HeightOneSpectrum (𝓞 F) → Prop}
    (h : ¬ P v) : resS F PP (adS F E (idemAd P)) = 0 := by
  refine resS_adS_eq_zero PP v hv _ ?_
  rw [idemAd_neg h, map_zero]; exact zero_lt_one

theorem resS_idemAd_pos (PP : Pl E) (v : HeightOneSpectrum (𝓞 F))
    (hv : v.asIdeal = PP.asIdeal.comap (algebraMap (𝓞 F) (𝓞 E))) {P : HeightOneSpectrum (𝓞 F) → Prop}
    (h : P v) : resS F PP (adS F E (idemAd P)) = 1 := by
  have h0 : resS F PP (adS F E (1 - idemAd P)) = 0 := by
    refine resS_adS_eq_zero PP v hv _ ?_
    have : (((1 - idemAd P : intAd F)) : Af F) v = 1 - ((idemAd P : intAd F) : Af F) v := rfl
    rw [this, idemAd_pos h, sub_self, map_zero]; exact zero_lt_one
  rw [map_sub, map_sub, map_one, map_one, sub_eq_zero] at h0
  exact h0.symm

theorem isUnit_intAd (a : intAd F) (h : ∀ v, Valued.v ((a : Af F) v) = 1) : IsUnit a := by
  have h0 : ∀ v, (a : Af F) v ≠ 0 := fun v h0 => by
    have := h v; rw [h0, map_zero] at this; exact zero_ne_one this
  refine IsUnit.of_mul_eq_one (mkAd (fun v => ((a : Af F) v)⁻¹) (fun v => ?_)) ?_
  · rw [HeightOneSpectrum.mem_adicCompletionIntegers, map_inv₀, h v, inv_one]
  · apply Subtype.ext
    refine FiniteAdeleRing.ext _ fun v => ?_
    show (a : Af F) v * ((a : Af F) v)⁻¹ = 1
    exact mul_inv_cancel₀ (h0 v)

def underPl (F : Type) [Field F] [NumberField F] [Algebra F E] (PP : Pl E) : HeightOneSpectrum (𝓞 F) where
  asIdeal := PP.asIdeal.comap (algebraMap (𝓞 F) (𝓞 E))
  isPrime := Ideal.comap_isPrime _ _
  ne_bot := by
    intro h
    have hN : ((Ideal.absNorm PP.asIdeal : ℕ) : 𝓞 F) ∈ PP.asIdeal.comap (algebraMap (𝓞 F) (𝓞 E)) := by
      rw [Ideal.mem_comap, map_natCast]; exact Ideal.absNorm_mem _
    rw [h, Ideal.mem_bot] at hN
    have : Ideal.absNorm PP.asIdeal = 0 := by exact_mod_cast hN
    exact PP.ne_bot (Ideal.absNorm_eq_zero_iff.1 this)

theorem underPl_asIdeal (PP : Pl E) :
    (underPl F PP).asIdeal = PP.asIdeal.comap (algebraMap (𝓞 F) (𝓞 E)) := rfl

theorem exists_overPl (v : HeightOneSpectrum (𝓞 F)) :
    ∃ PP : Pl E, v.asIdeal = PP.asIdeal.comap (algebraMap (𝓞 F) (𝓞 E)) := by
  have hinj : Function.Injective (algebraMap (𝓞 F) (𝓞 E)) :=
    FaithfulSMul.algebraMap_injective (𝓞 F) (𝓞 E)
  have : v.asIdeal.IsMaximal := v.isMaximal
  obtain ⟨Q, hQ, hQv⟩ := Ideal.exists_ideal_over_maximal_of_isIntegral (S := 𝓞 E) v.asIdeal (by
    rw [(RingHom.injective_iff_ker_eq_bot _).1 hinj]; exact bot_le)
  refine ⟨⟨Q, hQ.isPrime, ?_⟩, hQv.symm⟩
  intro h
  rw [h] at hQv
  apply v.ne_bot
  rw [← hQv]
  exact (RingHom.injective_iff_ker_eq_bot _).1 hinj

end ToolA

section ToolB

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]

def sigS (hc : CMData F E) : intAf F E →+* intAf F E :=
  ((sigR hc.sig (Af F)).comp (intAf F E).subtype).codRestrict (intAf F E)
    (fun s => Formalism.UG.P.csScale_sigR_mem hc.sig s.2)

theorem sigS_coe (hc : CMData F E) (s : intAf F E) :
    ((sigS hc s : intAf F E) : E ⊗[F] Af F) = sigR hc.sig (Af F) (s : E ⊗[F] Af F) := rfl

def starO (a : 𝓞 E) : 𝓞 E := ⟨star (a : E), Formalism.BasicNotions.Examples₂.star_isIntegral _ a.2⟩

theorem starO_coe (a : 𝓞 E) : ((starO a : 𝓞 E) : E) = star (a : E) := rfl

theorem starO_starO (a : 𝓞 E) : starO (starO a) = a := by
  apply RingOfIntegers.ext
  rw [starO_coe, starO_coe, star_star]

theorem sigS_oToS (hc : CMData F E) (a : 𝓞 E) : sigS hc (oToS F E a) = oToS F E (starO a) := by
  apply Subtype.ext
  rw [sigS_coe, oToS_coe, oToS_coe]
  exact Formalism.UG.P.csScale_sigR_incl hc.sig (algebraMap (𝓞 E) E a)

theorem sigS_adS (hc : CMData F E) (a : intAd F) : sigS hc (adS F E a) = adS F E a := by
  apply Subtype.ext
  rw [sigS_coe, adS_coe]
  simp [sigR]

theorem sigR_sigR (hc : CMData F E) (x : E ⊗[F] Af F) : sigR hc.sig (Af F) (sigR hc.sig (Af F) x) = x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => rw [map_add, map_add, hx, hy]
  | tmul e b =>
    show (hc.sig (hc.sig e)) ⊗ₜ[F] b = e ⊗ₜ[F] b
    have : hc.sig (hc.sig e) = e := star_star e
    rw [this]

theorem sigS_sigS (hc : CMData F E) (s : intAf F E) : sigS hc (sigS hc s) = s :=
  Subtype.ext (sigR_sigR hc _)

theorem IsConjPl.symm {PP PP' : Pl E} (h : IsConjPl PP PP') : IsConjPl PP' PP := by
  intro a b hab
  have : (a : E) = star (b : E) := by rw [hab, star_star]
  exact (h b a this).symm

theorem sigS_mem_idS (hc : CMData F E) {PP PP' : Pl E} (h : IsConjPl PP PP') {s : intAf F E}
    (hs : s ∈ idS F PP.asIdeal) : sigS hc s ∈ idS F PP'.asIdeal := by
  have hle : idS F PP.asIdeal ≤ (idS F PP'.asIdeal).comap (sigS hc) := by
    refine Ideal.map_le_iff_le_comap.2 fun a ha => ?_
    show sigS hc (oToS F E a) ∈ idS F PP'.asIdeal
    rw [sigS_oToS]
    exact Ideal.mem_map_of_mem _ ((h a (starO a) rfl).1 ha)
  exact hle hs

theorem resS_sigS_eq_zero_iff (hc : CMData F E) {PP PP' : Pl E} (h : IsConjPl PP PP') (s : intAf F E) :
    resS F PP' (sigS hc s) = 0 ↔ resS F PP s = 0 := by
  rw [resS_eq_zero_iff, resS_eq_zero_iff]
  constructor
  · intro hs
    have := sigS_mem_idS hc h.symm hs
    rwa [sigS_sigS] at this
  · exact sigS_mem_idS hc h

def starOHom : 𝓞 E →+* 𝓞 E where
  toFun := starO
  map_one' := by apply RingOfIntegers.ext; rw [starO_coe]; simp
  map_mul' a b := by apply RingOfIntegers.ext; rw [starO_coe]; simp [starO_coe]
  map_zero' := by apply RingOfIntegers.ext; rw [starO_coe]; simp
  map_add' a b := by apply RingOfIntegers.ext; rw [starO_coe]; simp [starO_coe]

def conjPl (PP : Pl E) : Pl E where
  asIdeal := PP.asIdeal.comap starOHom
  isPrime := Ideal.comap_isPrime _ _
  ne_bot := by
    obtain ⟨a, ha, ha0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot PP.ne_bot
    intro h
    have h1 : starO a ∈ PP.asIdeal.comap starOHom := by
      show starO (starO a) ∈ PP.asIdeal
      rw [starO_starO]; exact ha
    rw [h, Ideal.mem_bot] at h1
    apply ha0
    rw [← starO_starO a, h1]
    exact map_zero starOHom

theorem isConjPl_conjPl (PP : Pl E) : IsConjPl PP (conjPl PP) := by
  intro a b hab
  have hb : b = starO a := RingOfIntegers.ext hab
  subst hb
  show a ∈ PP.asIdeal ↔ starO (starO a) ∈ PP.asIdeal
  rw [starO_starO]

theorem IsConjPl.eq_conjPl {PP PP' : Pl E} (h : IsConjPl PP PP') : PP' = conjPl PP := by
  apply HeightOneSpectrum.ext
  ext b
  rw [← (h (starO b) b (by rw [starO_coe, star_star])), ← (isConjPl_conjPl PP (starO b) b (by rw [starO_coe, star_star]))]

theorem conjPl_conjPl (PP : Pl E) : conjPl (conjPl PP) = PP :=
  ((isConjPl_conjPl PP).symm.eq_conjPl).symm

theorem add_sigR_mem (hc : CMData F E) (x : E ⊗[F] Af F) :
    ∃ a : Af F, x + sigR hc.sig (Af F) x = (1 : E) ⊗ₜ[F] a := by
  induction x using TensorProduct.induction_on with
  | zero => exact ⟨0, by simp⟩
  | add x y hx hy =>
    obtain ⟨a, ha⟩ := hx
    obtain ⟨b, hb⟩ := hy
    refine ⟨a + b, ?_⟩
    rw [map_add, TensorProduct.tmul_add, ← ha, ← hb]; abel
  | tmul e b =>
    have h1 : sigR hc.sig (Af F) (e ⊗ₜ[F] b) = (star e) ⊗ₜ[F] b := rfl
    obtain ⟨f, hf⟩ := (hc.fixed (e + star e)).1 (by rw [star_add, star_star, add_comm])
    refine ⟨f • b, ?_⟩
    rw [h1, ← TensorProduct.add_tmul, ← hf, Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul]

theorem exists_adele_of_fixed (hc : CMData F E) (x : E ⊗[F] Af F) (hx : sigR hc.sig (Af F) x = x) :
    ∃ a : Af F, x = (1 : E) ⊗ₜ[F] a := by
  obtain ⟨a, ha⟩ := add_sigR_mem hc x
  rw [hx] at ha
  refine ⟨(2⁻¹ : F) • a, ?_⟩
  rw [TensorProduct.tmul_smul, ← ha, ← two_smul F x, smul_smul]
  norm_num

theorem mem_intAd_of_tmul_mem (a : Af F) (h : (1 : E) ⊗ₜ[F] a ∈ intAf F E) : a ∈ intAd F := by
  obtain ⟨d, hd0, hd⟩ := Formalism.UG.P.levelaf_adele_denom a
  obtain ⟨r, y, hy, e⟩ := Formalism.UG.P.integral_adele_approximation_holds F d hd0 _ hd
  have hdF : (algebraMap (𝓞 F) F d) ≠ 0 := by simpa using hd0
  set f : F := (algebraMap (𝓞 F) F d)⁻¹ * algebraMap (𝓞 F) F r with hf
  have e1 : a - y = algebraMap F (Af F) f := by
    have h1 : algebraMap F (Af F) (algebraMap (𝓞 F) F d) * (a - y) = algebraMap F (Af F) (algebraMap (𝓞 F) F r) := by
      rw [← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply, mul_sub, e]; ring
    calc a - y = algebraMap F (Af F) ((algebraMap (𝓞 F) F d)⁻¹ * algebraMap (𝓞 F) F d) * (a - y) := by
          rw [inv_mul_cancel₀ hdF, map_one, one_mul]
      _ = algebraMap F (Af F) (algebraMap (𝓞 F) F d)⁻¹ * (algebraMap F (Af F) (algebraMap (𝓞 F) F d) * (a - y)) := by
          rw [map_mul]; ring
      _ = algebraMap F (Af F) f := by rw [h1, hf, map_mul]
  have h2 : inclE (F := F) (Af F) (algebraMap F E f) ∈ intAf F E := by
    have h3 : (1 : E) ⊗ₜ[F] (a - y) ∈ intAf F E := by
      rw [TensorProduct.tmul_sub]
      exact sub_mem h (Subring.subset_closure (Or.inr ⟨⟨y, hy⟩, rfl⟩))
    rw [e1, Algebra.algebraMap_eq_smul_one, ← TensorProduct.smul_tmul, ← Algebra.algebraMap_eq_smul_one] at h3
    exact h3
  have h4 : IsIntegral ℤ f :=
    (isIntegral_algebraMap_iff (algebraMap F E).injective).1 (Formalism.UG.P.csGlob_int (F := F) _ h2)
  have h5 : algebraMap F (Af F) f ∈ intAd F := by
    have e5 : algebraMap F (Af F) f = algebraMap (𝓞 F) (Af F) (⟨f, h4⟩ : 𝓞 F) :=
      (IsScalarTower.algebraMap_apply (𝓞 F) F (Af F) (⟨f, h4⟩ : 𝓞 F)).symm
    rw [e5]
    exact Formalism.UG.P.levelaf_int_mem (⟨f, h4⟩ : 𝓞 F)
  have : a = y + algebraMap F (Af F) f := by rw [← e1]; ring
  rw [this]
  exact add_mem hy h5

theorem isUnit_of_resS_ne_zero (hc : CMData F E) (c : intAf F E) (h : ∀ PP : Pl E, resS F PP c ≠ 0) :
    IsUnit c := by
  obtain ⟨a, ha⟩ := exists_adele_of_fixed hc ((c * sigS hc c : intAf F E) : E ⊗[F] Af F) (by
    rw [← sigS_coe, map_mul, sigS_sigS, mul_comm])
  have haI : a ∈ intAd F := mem_intAd_of_tmul_mem (E := E) a (by rw [← ha]; exact (c * sigS hc c).2)
  have hN : c * sigS hc c = adS F E ⟨a, haI⟩ := Subtype.ext ha
  have hu : IsUnit (⟨a, haI⟩ : intAd F) := by
    refine isUnit_intAd _ fun v => ?_
    obtain ⟨PP, hPP⟩ := exists_overPl (E := E) v
    have hle : Valued.v (a v) ≤ 1 := (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).1 (haI v)
    refine le_antisymm hle (not_lt.1 fun hlt => ?_)
    have h0 := resS_adS_eq_zero PP v hPP ⟨a, haI⟩ hlt
    rw [← hN, map_mul] at h0
    rcases mul_eq_zero.1 h0 with h1 | h1
    · exact h PP h1
    · exact h (conjPl PP) ((resS_sigS_eq_zero_iff hc (isConjPl_conjPl PP).symm c).1 h1)
  have : IsUnit (c * sigS hc c) := by rw [hN]; exact hu.map _
  exact isUnit_of_mul_isUnit_left this

theorem isUnit_matrix_of_resS {n : ℕ} (hc : CMData F E) (M : Matrix (Fin n) (Fin n) (intAf F E))
    (h : ∀ PP : Pl E, (M.map (resS F PP)).det ≠ 0) : IsUnit M := by
  rw [Matrix.isUnit_iff_isUnit_det]
  refine isUnit_of_resS_ne_zero hc _ fun PP => ?_
  rw [RingHom.map_det]
  exact h PP

end ToolB

section CT

variable {A : Type} [CommRing A] {n : Type} [Fintype n] [DecidableEq n]

theorem cT_cT (σ : A →+* A) (hσ : ∀ a, σ (σ a) = a) (M : Matrix n n A) : cT σ (cT σ M) = M := by
  ext i j
  exact hσ _

theorem cT_add (σ : A →+* A) (M N : Matrix n n A) : cT σ (M + N) = cT σ M + cT σ N := by
  ext i j
  exact map_add σ _ _

theorem cT_smul (σ : A →+* A) (c : A) (M : Matrix n n A) : cT σ (c • M) = σ c • cT σ M := by
  ext i j
  exact map_mul σ _ _

theorem UJ_conj_iff (σ : A →+* A) (J : Matrix n n A) (b g : GL n A) :
    b * g * b⁻¹ ∈ UJ σ J ↔
      cT σ (g : Matrix n n A) * (cT σ (b : Matrix n n A) * J * (b : Matrix n n A)) * (g : Matrix n n A) =
        cT σ (b : Matrix n n A) * J * (b : Matrix n n A) := by
  have h1 : cT σ (b : Matrix n n A) * cT σ ((b⁻¹ : GL n A) : Matrix n n A) = 1 := by
    rw [← cT_mul, Units.inv_mul, cT_one]
  have h1' : cT σ ((b⁻¹ : GL n A) : Matrix n n A) * cT σ (b : Matrix n n A) = 1 := by
    rw [← cT_mul, Units.mul_inv, cT_one]
  have h2 : ((b⁻¹ : GL n A) : Matrix n n A) * (b : Matrix n n A) = 1 := Units.inv_mul b
  have h2' : (b : Matrix n n A) * ((b⁻¹ : GL n A) : Matrix n n A) = 1 := Units.mul_inv b
  have hm : b * g * b⁻¹ ∈ UJ σ J ↔
      cT σ ((b⁻¹ : GL n A) : Matrix n n A) * (cT σ (g : Matrix n n A) * cT σ (b : Matrix n n A)) * J *
        ((b : Matrix n n A) * (g : Matrix n n A) * ((b⁻¹ : GL n A) : Matrix n n A)) = J := by
    show cT σ ((b * g * b⁻¹ : GL n A) : Matrix n n A) * J * ((b * g * b⁻¹ : GL n A) : Matrix n n A) = J ↔ _
    rw [Units.val_mul, Units.val_mul, cT_mul, cT_mul]
  rw [hm]
  constructor
  · intro h
    calc cT σ (g : Matrix n n A) * (cT σ (b : Matrix n n A) * J * (b : Matrix n n A)) * (g : Matrix n n A)
        = (cT σ (b : Matrix n n A) * cT σ ((b⁻¹ : GL n A) : Matrix n n A)) *
            (cT σ (g : Matrix n n A) * cT σ (b : Matrix n n A)) * J *
            ((b : Matrix n n A) * (g : Matrix n n A) * (((b⁻¹ : GL n A) : Matrix n n A) * (b : Matrix n n A))) := by
          rw [h1, h2]; simp only [Matrix.one_mul, Matrix.mul_one, Matrix.mul_assoc]
      _ = cT σ (b : Matrix n n A) * (cT σ ((b⁻¹ : GL n A) : Matrix n n A) *
            (cT σ (g : Matrix n n A) * cT σ (b : Matrix n n A)) * J *
            ((b : Matrix n n A) * (g : Matrix n n A) * ((b⁻¹ : GL n A) : Matrix n n A))) * (b : Matrix n n A) := by
          simp only [Matrix.mul_assoc]
      _ = cT σ (b : Matrix n n A) * J * (b : Matrix n n A) := by rw [h]
  · intro h
    calc cT σ ((b⁻¹ : GL n A) : Matrix n n A) * (cT σ (g : Matrix n n A) * cT σ (b : Matrix n n A)) * J *
          ((b : Matrix n n A) * (g : Matrix n n A) * ((b⁻¹ : GL n A) : Matrix n n A))
        = cT σ ((b⁻¹ : GL n A) : Matrix n n A) *
            (cT σ (g : Matrix n n A) * (cT σ (b : Matrix n n A) * J * (b : Matrix n n A)) * (g : Matrix n n A)) *
            ((b⁻¹ : GL n A) : Matrix n n A) := by simp only [Matrix.mul_assoc]
      _ = (cT σ ((b⁻¹ : GL n A) : Matrix n n A) * cT σ (b : Matrix n n A)) * J *
            ((b : Matrix n n A) * ((b⁻¹ : GL n A) : Matrix n n A)) := by
          rw [h]; simp only [Matrix.mul_assoc]
      _ = J := by rw [h1', h2', Matrix.one_mul, Matrix.mul_one]

end CT

section Gram

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] {n : ℕ}

def gramA (hc : CMData F E) (J : Matrix (Fin n) (Fin n) E) (β : GL (Fin n) (E ⊗[F] Af F)) :
    Matrix (Fin n) (Fin n) (E ⊗[F] Af F) :=
  cT (sigR hc.sig (Af F)) (β : Matrix (Fin n) (Fin n) (E ⊗[F] Af F)) * J.map (inclE (F := F) (Af F)) *
    (β : Matrix (Fin n) (Fin n) (E ⊗[F] Af F))

theorem frame_mulVec_mem {β : GL (Fin n) (E ⊗[F] Af F)} {L : Submodule (𝓞 E) (Fin n → E)} (hβ : IsFrame β L)
    (y : Fin n → E ⊗[F] Af F) (hy : ∀ i, y i ∈ intAf F E) :
    (β : Matrix (Fin n) (Fin n) (E ⊗[F] Af F)) *ᵥ y ∈ hatL (F := F) L := by
  rw [hβ]
  intro i
  rw [Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec]
  exact hy i

theorem single_mem_intAf (j i : Fin n) : (Pi.single j (1 : E ⊗[F] Af F) : Fin n → E ⊗[F] Af F) i ∈ intAf F E := by
  rw [Pi.single_apply]
  split_ifs
  · exact one_mem _
  · exact zero_mem _

theorem intGL_coe (y : GL (Fin n) (intAf F E)) :
    ((intGL F E n y : GL (Fin n) (E ⊗[F] Af F)) : Matrix (Fin n) (Fin n) (E ⊗[F] Af F)) =
      (y : Matrix (Fin n) (Fin n) (intAf F E)).map (intAf F E).subtype := rfl

theorem map_subtype_injective :
    Function.Injective (fun M : Matrix (Fin n) (Fin n) (intAf F E) => M.map (intAf F E).subtype) := by
  intro X Y h
  ext i j
  exact congrFun (congrFun h i) j

theorem cT_map_subtype (hc : CMData F E) (M : Matrix (Fin n) (Fin n) (intAf F E)) :
    (cT (sigS hc) M).map (intAf F E).subtype = cT (sigR hc.sig (Af F)) (M.map (intAf F E).subtype) := by
  ext i j
  rfl

theorem exists_gramS (hc : CMData F E) {J : Matrix (Fin n) (Fin n) E} {L : Submodule (𝓞 E) (Fin n → E)}
    {β : GL (Fin n) (E ⊗[F] Af F)} (hU : IsDefUnimod hc J L) (hβ : IsFrame β L) :
    ∃ G : GL (Fin n) (intAf F E),
      (G : Matrix (Fin n) (Fin n) (intAf F E)).map (intAf F E).subtype = gramA hc J β := by
  have hint : ∀ x ∈ L, ∀ z ∈ L, IsIntegral ℤ (((1 : ℤ) : E) * hform (hc.sig : E →+* E) J x z) := by
    intro x hx z hz
    have hz' : z ∈ dualSet (hc.sig : E →+* E) J L := by rw [hU.selfdual]; exact hz
    obtain ⟨a, ha⟩ := hz' x hx
    rw [Int.cast_one, one_mul, ← ha]
    exact RingOfIntegers.isIntegral_coe a
  have hG1 : ∀ i j, gramA hc J β i j ∈ intAf F E := by
    intro i j
    have := Formalism.UG.P.csScale_latS hc.sig J L 1 hint (frame_mulVec_mem hβ _ (single_mem_intAf i))
      (frame_mulVec_mem hβ _ (single_mem_intAf j))
    rw [Int.cast_one, map_one, one_mul, Formalism.UG.P.hform_mulVec, Formalism.UG.P.hform_single] at this
    exact this
  have hJu : IsUnit (J.map (inclE (F := F) (Af F))) := by
    rw [Matrix.isUnit_iff_isUnit_det]
    have : (J.map (inclE (F := F) (Af F))).det = inclE (F := F) (Af F) J.det :=
      (RingHom.map_det (inclE (F := F) (Af F)) J).symm
    rw [this]
    exact hU.unit.map _
  obtain ⟨Ju, hJu'⟩ := hJu
  let cβ : GL (Fin n) (E ⊗[F] Af F) :=
    ⟨cT (sigR hc.sig (Af F)) (β : Matrix (Fin n) (Fin n) (E ⊗[F] Af F)),
      cT (sigR hc.sig (Af F)) ((β⁻¹ : GL (Fin n) (E ⊗[F] Af F)) : Matrix (Fin n) (Fin n) (E ⊗[F] Af F)),
      by rw [← cT_mul, Units.inv_mul, cT_one], by rw [← cT_mul, Units.mul_inv, cT_one]⟩
  set Gu : GL (Fin n) (E ⊗[F] Af F) := cβ * Ju * β with hGu
  have hGv : (Gu : Matrix (Fin n) (Fin n) (E ⊗[F] Af F)) = gramA hc J β := by
    rw [hGu, Units.val_mul, Units.val_mul, hJu']
    rfl
  have hG2 : ∀ i j, ((Gu⁻¹ : GL (Fin n) (E ⊗[F] Af F)) : Matrix (Fin n) (Fin n) (E ⊗[F] Af F)) i j ∈ intAf F E := by
    intro i j
    set u : Fin n → E ⊗[F] Af F :=
      ((Gu⁻¹ : GL (Fin n) (E ⊗[F] Af F)) : Matrix (Fin n) (Fin n) (E ⊗[F] Af F)) *ᵥ Pi.single j 1 with hu
    have hw : (β : Matrix (Fin n) (Fin n) (E ⊗[F] Af F)) *ᵥ u ∈ hatL (F := F) L := by
      refine hat_selfdual hc.sig J L hU.lat.span_eq_top hU.selfdual _ fun l hl => ?_
      set y : Fin n → E ⊗[F] Af F :=
        ((β⁻¹ : GL (Fin n) (E ⊗[F] Af F)) : Matrix (Fin n) (Fin n) (E ⊗[F] Af F)) *ᵥ
          (fun i => inclE (F := F) (Af F) (l i)) with hy
      have hyS : ∀ i, y i ∈ intAf F E :=
        (hβ _).1 (Submodule.subset_span ⟨l, hl, rfl⟩)
      have e : (fun i => inclE (F := F) (Af F) (l i)) = (β : Matrix (Fin n) (Fin n) (E ⊗[F] Af F)) *ᵥ y := by
        rw [hy, Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec]
      rw [e, Formalism.UG.P.hform_mulVec, Formalism.UG.P.hform_eq_dot]
      have e2 : (cT (sigR hc.sig (Af F)) (β : Matrix (Fin n) (Fin n) (E ⊗[F] Af F)) *
          J.map (inclE (F := F) (Af F)) * (β : Matrix (Fin n) (Fin n) (E ⊗[F] Af F))) *ᵥ u = Pi.single j 1 := by
        have : (cT (sigR hc.sig (Af F)) (β : Matrix (Fin n) (Fin n) (E ⊗[F] Af F)) *
          J.map (inclE (F := F) (Af F)) * (β : Matrix (Fin n) (Fin n) (E ⊗[F] Af F))) =
            (Gu : Matrix (Fin n) (Fin n) (E ⊗[F] Af F)) := hGv.symm
        rw [this, hu, Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec]
      rw [e2, dotProduct_single, mul_one]
      exact Formalism.UG.P.csScale_sigR_mem hc.sig (hyS j)
    have h3 := (hβ _).1 hw i
    rw [Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec, hu, Matrix.mulVec_single_one] at h3
    exact h3
  obtain ⟨G, hG⟩ := Formalism.UG.P.levelaf_mem_range_of_integral (intAf F E) Gu
    ⟨fun i j => ⟨(Gu : Matrix (Fin n) (Fin n) (E ⊗[F] Af F)) i j, by rw [hGv]; exact hG1 i j⟩, by ext i j; rfl⟩
    ⟨fun i j => ⟨((Gu⁻¹ : GL (Fin n) (E ⊗[F] Af F)) : Matrix (Fin n) (Fin n) (E ⊗[F] Af F)) i j, hG2 i j⟩,
      by ext i j; rfl⟩
  refine ⟨G, ?_⟩
  rw [← hGv, ← hG]
  rfl

theorem gramA_herm (hc : CMData F E) {J : Matrix (Fin n) (Fin n) E} (hJ : IsHerm (hc.sig : E →+* E) J)
    (β : GL (Fin n) (E ⊗[F] Af F)) : cT (sigR hc.sig (Af F)) (gramA hc J β) = gramA hc J β := by
  have hJ' : cT (sigR hc.sig (Af F)) (J.map (inclE (F := F) (Af F))) = J.map (inclE (F := F) (Af F)) := by
    ext i j
    show sigR hc.sig (Af F) (inclE (F := F) (Af F) (J j i)) = inclE (F := F) (Af F) (J i j)
    rw [Formalism.UG.P.csScale_sigR_incl]
    exact congrArg _ (congrFun (congrFun hJ i) j)
  unfold gramA
  rw [cT_mul, cT_mul, cT_cT _ (sigR_sigR hc), hJ', Matrix.mul_assoc]

theorem gramS_herm (hc : CMData F E) {J : Matrix (Fin n) (Fin n) E} (hJ : IsHerm (hc.sig : E →+* E) J)
    {β : GL (Fin n) (E ⊗[F] Af F)} {G : GL (Fin n) (intAf F E)}
    (hG : (G : Matrix (Fin n) (Fin n) (intAf F E)).map (intAf F E).subtype = gramA hc J β) :
    cT (sigS hc) (G : Matrix (Fin n) (Fin n) (intAf F E)) = (G : Matrix (Fin n) (Fin n) (intAf F E)) := by
  apply map_subtype_injective
  show (cT (sigS hc) (G : Matrix (Fin n) (Fin n) (intAf F E))).map (intAf F E).subtype = _
  rw [cT_map_subtype, hG, gramA_herm hc hJ]
  exact hG.symm

theorem frGL_mem_UA_iff (hc : CMData F E) {J : Matrix (Fin n) (Fin n) E}
    {β : GL (Fin n) (E ⊗[F] Af F)} {G : GL (Fin n) (intAf F E)}
    (hG : (G : Matrix (Fin n) (Fin n) (intAf F E)).map (intAf F E).subtype = gramA hc J β)
    (y : GL (Fin n) (intAf F E)) :
    frGL β y ∈ UA hc J ↔
      cT (sigS hc) (y : Matrix (Fin n) (Fin n) (intAf F E)) * (G : Matrix (Fin n) (Fin n) (intAf F E)) *
        (y : Matrix (Fin n) (Fin n) (intAf F E)) = (G : Matrix (Fin n) (Fin n) (intAf F E)) := by
  have h1 : frGL β y = β * intGL F E n y * β⁻¹ := by
    simp [frGL]
  rw [h1]
  have h2 := UJ_conj_iff (sigR hc.sig (Af F)) (J.map (inclE (F := F) (Af F))) β (intGL F E n y)
  refine h2.trans ?_
  rw [intGL_coe, ← cT_map_subtype]
  show _ * gramA hc J β * _ = gramA hc J β ↔ _
  rw [← hG, ← Matrix.map_mul, ← Matrix.map_mul]
  exact map_subtype_injective.eq_iff

end Gram

theorem level_conjugate : KgConj := by
  intro F E _ _ _ _ _ _ hc n J L β PP PP' hU hβ hconj x hxU hx
  obtain ⟨⟨y, rfl⟩, hred⟩ := mem_princAt.1 hx
  rw [redFn_frGL] at hred
  obtain ⟨G, hG⟩ := exists_gramS hc hU hβ
  have hy := (frGL_mem_UA_iff hc hG y).1 hxU
  refine mem_princAt.2 ⟨⟨y, rfl⟩, ?_⟩
  rw [redFn_frGL]
  have hbar : (y : Matrix (Fin n) (Fin n) (intAf F E)).map (resS F PP) = 1 := congrArg Units.val hred
  have h1 := congrArg (fun M : Matrix (Fin n) (Fin n) (intAf F E) => M.map (resS F PP)) hy
  simp only [Matrix.map_mul] at h1
  rw [hbar, Matrix.mul_one] at h1
  have hGu : IsUnit ((G : Matrix (Fin n) (Fin n) (intAf F E)).map (resS F PP)) := ⟨bc (resS F PP) G, rfl⟩
  have h2 : (cT (sigS hc) (y : Matrix (Fin n) (Fin n) (intAf F E))).map (resS F PP) = 1 :=
    hGu.mul_right_cancel (by rw [h1, Matrix.one_mul])
  apply Units.ext
  ext i j
  show resS F PP' ((y : Matrix (Fin n) (Fin n) (intAf F E)) i j) = (1 : Matrix (Fin n) (Fin n) (kP PP')) i j
  have h3 : resS F PP (sigS hc ((y : Matrix (Fin n) (Fin n) (intAf F E)) i j)) =
      (1 : Matrix (Fin n) (Fin n) (kP PP)) j i := congrFun (congrFun h2 j) i
  by_cases hij : i = j
  · subst hij
    rw [Matrix.one_apply_eq] at h3 ⊢
    have h4 : resS F PP (sigS hc ((y : Matrix (Fin n) (Fin n) (intAf F E)) i i - 1)) = 0 := by
      rw [map_sub, map_sub, h3, map_one, map_one, sub_self]
    have h5 := (resS_sigS_eq_zero_iff hc hconj.symm _).1 h4
    rwa [map_sub, map_one, sub_eq_zero] at h5
  · rw [Matrix.one_apply_ne (Ne.symm hij)] at h3
    rw [Matrix.one_apply_ne hij]
    exact (resS_sigS_eq_zero_iff hc hconj.symm _).1 h3

section Cayley

variable {A : Type} [CommRing A] {n : Type} [Fintype n] [DecidableEq n]

theorem unitary_of_herm (σ : A →+* A) (hσ : ∀ a, σ (σ a) = a) (G Pu Qu : GL n A) (N : Matrix n n A) (c : A)
    (hG : cT σ (G : Matrix n n A) = G) (hN : cT σ N = N) (hP : (Pu : Matrix n n A) = G + c • N)
    (hQ : (Qu : Matrix n n A) = G + σ c • N) :
    cT σ ((G⁻¹ * Pu * Qu⁻¹ * G : GL n A) : Matrix n n A) * (G : Matrix n n A) *
      ((G⁻¹ * Pu * Qu⁻¹ * G : GL n A) : Matrix n n A) = (G : Matrix n n A) := by
  set g : Matrix n n A := (G : Matrix n n A) with hg
  set gi : Matrix n n A := ((G⁻¹ : GL n A) : Matrix n n A) with hgi
  set p : Matrix n n A := (Pu : Matrix n n A) with hp
  set pi : Matrix n n A := ((Pu⁻¹ : GL n A) : Matrix n n A) with hpi
  set q : Matrix n n A := (Qu : Matrix n n A) with hq
  set qi : Matrix n n A := ((Qu⁻¹ : GL n A) : Matrix n n A) with hqi
  have hggi : g * gi = 1 := Units.mul_inv G
  have hgig : gi * g = 1 := Units.inv_mul G
  have hppi : p * pi = 1 := Units.mul_inv Pu
  have hpip : pi * p = 1 := Units.inv_mul Pu
  have hqqi : q * qi = 1 := Units.mul_inv Qu
  have hcp : cT σ p = q := by rw [hP, cT_add, cT_smul, hG, hN, hQ]
  have hcq : cT σ q = p := by rw [hQ, cT_add, cT_smul, hσ, hG, hN, hP]
  have hcqi : cT σ qi = pi := by
    have h1 : cT σ qi * p = 1 := by rw [← hcq, ← cT_mul, hqqi, cT_one]
    calc cT σ qi = cT σ qi * (p * pi) := by rw [hppi, Matrix.mul_one]
      _ = pi := by rw [← Matrix.mul_assoc, h1, Matrix.one_mul]
  have hcgi : cT σ gi = gi := by
    have h1 : cT σ gi * g = 1 := by
      calc cT σ gi * g = cT σ gi * cT σ g := by rw [hG]
        _ = 1 := by rw [← cT_mul, hggi, cT_one]
    calc cT σ gi = cT σ gi * (g * gi) := by rw [hggi, Matrix.mul_one]
      _ = gi := by rw [← Matrix.mul_assoc, h1, Matrix.one_mul]
  have hexp : ∀ a b : A, (g + a • N) * gi * (g + b • N) = g + b • N + a • N + (a * b) • (N * gi * N) := by
    intro a b
    calc (g + a • N) * gi * (g + b • N) = (1 + a • (N * gi)) * (g + b • N) := by
          rw [Matrix.add_mul, Matrix.smul_mul, hggi]
      _ = g + b • N + (a • (N * gi * g) + (a * b) • (N * gi * N)) := by
          rw [Matrix.add_mul, Matrix.one_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.smul_mul, Matrix.mul_smul,
            smul_smul]
      _ = g + b • N + a • N + (a * b) • (N * gi * N) := by
          rw [Matrix.mul_assoc N gi g, hgig, Matrix.mul_one, ← add_assoc]
  have key : q * gi * p = p * gi * q := by
    rw [hP, hQ, hexp, hexp, mul_comm c (σ c), add_right_comm g (c • N) (σ c • N)]
  have hval : ((G⁻¹ * Pu * Qu⁻¹ * G : GL n A) : Matrix n n A) = gi * p * qi * g := by
    rw [Units.val_mul, Units.val_mul, Units.val_mul]
  rw [hval, cT_mul, cT_mul, cT_mul, hG, hcqi, hcp, hcgi]
  calc g * (pi * (q * gi)) * g * (gi * p * qi * g) = g * pi * (q * gi * (g * gi) * p) * qi * g := by
        simp only [Matrix.mul_assoc]
    _ = g * pi * (p * gi * q) * qi * g := by rw [hggi, Matrix.mul_one, key]
    _ = g * (pi * p) * gi * (q * qi) * g := by simp only [Matrix.mul_assoc]
    _ = g := by rw [hpip, hqqi, Matrix.mul_one, Matrix.mul_one, hggi, Matrix.one_mul]

theorem map_smulR {B : Type} [CommRing B] (f : A →+* B) (r : A) (M : Matrix n n A) :
    (r • M).map f = f r • M.map f := by
  ext i j
  exact map_mul f _ _

theorem det_cT (σ : A →+* A) (M : Matrix n n A) : (cT σ M).det = σ M.det := by
  unfold cT
  rw [Matrix.det_transpose]
  exact (RingHom.map_det σ M).symm

end Cayley

theorem crtPl {E : Type} [Field E] [NumberField E] (s : Finset (Pl E)) (x : Pl E → 𝓞 E) :
    ∃ a : 𝓞 E, ∀ PP ∈ s, a - x PP ∈ PP.asIdeal := by
  obtain ⟨a, ha⟩ := IsDedekindDomain.exists_forall_sub_mem_ideal (s := s) (fun PP : Pl E => PP.asIdeal)
    (fun _ => 1) (fun PP _ => PP.prime) (fun PP _ PP' _ h h' => h (HeightOneSpectrum.ext h'))
    (fun PP => x PP.1)
  exact ⟨a, fun PP hPP => by simpa using ha PP hPP⟩

theorem exists_selector (F : Type) {E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (T : Finset (Pl E)) :
    ∃ c : intAf F E, (∀ QQ ∈ T, resS F QQ c = 1) ∧ ∀ QQ : Pl E, QQ ∉ T → resS F QQ c = 0 := by
  classical
  set D : ℕ := ∏ PP ∈ T, Ideal.absNorm PP.asIdeal with hDdef
  have hD0 : D ≠ 0 := Finset.prod_ne_zero_iff.2 fun PP _ h => PP.ne_bot (Ideal.absNorm_eq_zero_iff.1 h)
  have hD0E : (D : 𝓞 E) ≠ 0 := by exact_mod_cast hD0
  have hDT : ∀ PP ∈ T, (D : 𝓞 E) ∈ PP.asIdeal := by
    intro PP hPP
    obtain ⟨k, hk⟩ := Finset.dvd_prod_of_mem (fun PP : Pl E => Ideal.absNorm PP.asIdeal) hPP
    rw [hDdef, hk]
    push_cast
    exact Ideal.mul_mem_right _ _ (Ideal.absNorm_mem _)
  obtain ⟨c0, hc0⟩ := crtPl (primesOf (D : 𝓞 E)) (fun PP => if PP ∈ T then 1 else 0)
  set P : HeightOneSpectrum (𝓞 F) → Prop := fun v => (D : 𝓞 F) ∈ v.asIdeal with hP
  have hPiff : ∀ QQ : Pl E, P (underPl F QQ) ↔ (D : 𝓞 E) ∈ QQ.asIdeal := by
    intro QQ
    show (D : 𝓞 F) ∈ QQ.asIdeal.comap (algebraMap (𝓞 F) (𝓞 E)) ↔ _
    rw [Ideal.mem_comap, map_natCast]
  refine ⟨adS F E (idemAd P) * oToS F E c0, ?_, ?_⟩
  · intro QQ hQ
    have h1 := hc0 QQ (mem_primesOf.2 ⟨hD0E, hDT QQ hQ⟩)
    rw [if_pos hQ, ← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_one, sub_eq_zero] at h1
    rw [map_mul, resS_idemAd_pos QQ (underPl F QQ) rfl ((hPiff QQ).2 (hDT QQ hQ)), resS_oToS, h1, one_mul]
  · intro QQ hQ
    by_cases hDQ : (D : 𝓞 E) ∈ QQ.asIdeal
    · have h1 := hc0 QQ (mem_primesOf.2 ⟨hD0E, hDQ⟩)
      rw [if_neg hQ, sub_zero, ← Ideal.Quotient.eq_zero_iff_mem] at h1
      rw [map_mul, resS_oToS, h1, mul_zero]
    · rw [map_mul, resS_idemAd_neg QQ (underPl F QQ) rfl (fun h => hDQ ((hPiff QQ).1 h)), zero_mul]

theorem exists_matrix_lift (F : Type) {E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {n : ℕ} (T : Finset (Pl E)) (y : ∀ PP : ↥T, Matrix (Fin n) (Fin n) (kP PP.1)) :
    ∃ Y : Matrix (Fin n) (Fin n) (intAf F E), ∀ PP : ↥T, Y.map (resS F PP.1) = y PP := by
  classical
  have hlift : ∀ (PP : Pl E) (z : kP PP), ∃ a : 𝓞 E, Ideal.Quotient.mk PP.asIdeal a = z :=
    fun PP z => Ideal.Quotient.mk_surjective z
  choose lift hlift using hlift
  choose M0 hM0 using fun i j : Fin n => crtPl T (fun PP => if h : PP ∈ T then lift PP (y ⟨PP, h⟩ i j) else 0)
  refine ⟨fun i j => oToS F E (M0 i j), fun PP => ?_⟩
  ext i j
  show resS F PP.1 (oToS F E (M0 i j)) = _
  have h1 := hM0 i j PP.1 PP.2
  rw [dif_pos PP.2, ← Ideal.Quotient.eq_zero_iff_mem, map_sub, hlift, sub_eq_zero] at h1
  rw [resS_oToS, h1]

section Surj

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] {n : ℕ}

theorem resS_sigS_selector (hc : CMData F E) {T : Finset (Pl E)} {c : intAf F E}
    (hc1 : ∀ QQ ∈ T, resS F QQ c = 1) (hc2 : ∀ QQ : Pl E, QQ ∉ T → resS F QQ c = 0) :
    (∀ QQ : Pl E, conjPl QQ ∈ T → resS F QQ (sigS hc c) = 1) ∧
      ∀ QQ : Pl E, conjPl QQ ∉ T → resS F QQ (sigS hc c) = 0 := by
  constructor
  · intro QQ hQ
    have h1 : resS F (conjPl QQ) (c - 1) = 0 := by rw [map_sub, hc1 _ hQ, map_one, sub_self]
    have h2 := (resS_sigS_eq_zero_iff hc (isConjPl_conjPl QQ).symm (c - 1)).2 h1
    rwa [map_sub, map_sub, map_one, map_one, sub_eq_zero] at h2
  · exact fun QQ hQ => (resS_sigS_eq_zero_iff hc (isConjPl_conjPl QQ).symm c).2 (hc2 _ hQ)

set_option maxHeartbeats 800000 in

theorem exists_unitary_lift (hc : CMData F E) (G : GL (Fin n) (intAf F E))
    (hGh : cT (sigS hc) (G : Matrix (Fin n) (Fin n) (intAf F E)) = (G : Matrix (Fin n) (Fin n) (intAf F E)))
    (T : Finset (Pl E)) (hT : IsSplitSet T) (y : ∀ PP : ↥T, GL (Fin n) (kP PP.1)) :
    ∃ z : GL (Fin n) (intAf F E),
      cT (sigS hc) (z : Matrix (Fin n) (Fin n) (intAf F E)) * (G : Matrix (Fin n) (Fin n) (intAf F E)) *
        (z : Matrix (Fin n) (Fin n) (intAf F E)) = (G : Matrix (Fin n) (Fin n) (intAf F E)) ∧
      ∀ PP : ↥T, bc (resS F PP.1) z = y PP := by
  classical
  obtain ⟨c, hc1, hc2⟩ := exists_selector F T
  obtain ⟨hs1, hs2⟩ := resS_sigS_selector hc hc1 hc2
  obtain ⟨Y, hY⟩ := exists_matrix_lift F T (fun PP => ((y PP : GL (Fin n) (kP PP.1)) : Matrix (Fin n) (Fin n) (kP PP.1)))
  have hsplit : ∀ QQ ∈ T, conjPl QQ ∉ T := fun QQ hQ h => hT QQ hQ _ h (isConjPl_conjPl QQ)
  set g : Matrix (Fin n) (Fin n) (intAf F E) := (G : Matrix (Fin n) (Fin n) (intAf F E)) with hg
  set M : Matrix (Fin n) (Fin n) (intAf F E) := Y - 1 with hM
  set N : Matrix (Fin n) (Fin n) (intAf F E) := c • (g * M) + sigS hc c • (cT (sigS hc) M * g) with hN
  have hNh : cT (sigS hc) N = N := by
    rw [hN, cT_add, cT_smul, cT_smul, cT_mul, cT_mul, cT_cT _ (sigS_sigS hc), sigS_sigS, hGh, add_comm]
  have hNbar : ∀ QQ : Pl E, N.map (resS F QQ) = resS F QQ c • (g.map (resS F QQ) * M.map (resS F QQ)) +
      resS F QQ (sigS hc c) • ((cT (sigS hc) M).map (resS F QQ) * g.map (resS F QQ)) := by
    intro QQ
    rw [hN, Matrix.map_add _ (map_add _), map_smulR, map_smulR, Matrix.map_mul, Matrix.map_mul]
  have hgdet : ∀ QQ : Pl E, (g.map (resS F QQ)).det ≠ 0 := by
    intro QQ
    have : IsUnit (g.map (resS F QQ)) := ⟨bc (resS F QQ) G, rfl⟩
    exact ((Matrix.isUnit_iff_isUnit_det _).1 this).ne_zero
  have hone : ∀ QQ : Pl E, (1 : Matrix (Fin n) (Fin n) (intAf F E)).map (resS F QQ) = 1 := fun QQ =>
    Matrix.map_one _ (map_zero _) (map_one _)
  have hYM : Y = 1 + M := by rw [hM]; abel
  have hPbar1 : ∀ QQ (h : QQ ∈ T), (g + c • N).map (resS F QQ) =
      g.map (resS F QQ) * ((y ⟨QQ, h⟩ : GL (Fin n) (kP QQ)) : Matrix (Fin n) (Fin n) (kP QQ)) := by
    intro QQ h
    rw [Matrix.map_add _ (map_add _), map_smulR, hNbar, hc1 QQ h, hs2 QQ (hsplit QQ h), one_smul, one_smul,
      zero_smul, add_zero, ← hY ⟨QQ, h⟩, hYM, Matrix.map_add _ (map_add _), hone, Matrix.mul_add, Matrix.mul_one]
  have hPbar2 : ∀ QQ : Pl E, QQ ∉ T → (g + c • N).map (resS F QQ) = g.map (resS F QQ) := by
    intro QQ h
    rw [Matrix.map_add _ (map_add _), map_smulR, hc2 QQ h, zero_smul, add_zero]
  have hQbar2 : ∀ QQ : Pl E, conjPl QQ ∉ T → (g + sigS hc c • N).map (resS F QQ) = g.map (resS F QQ) := by
    intro QQ h
    rw [Matrix.map_add _ (map_add _), map_smulR, hs2 QQ h, zero_smul, add_zero]
  have hQbar1 : ∀ QQ : Pl E, conjPl QQ ∈ T → (g + sigS hc c • N).map (resS F QQ) =
      (cT (sigS hc) Y).map (resS F QQ) * g.map (resS F QQ) := by
    intro QQ h
    have hQT : QQ ∉ T := fun h' => hsplit QQ h' h
    rw [Matrix.map_add _ (map_add _), map_smulR, hNbar, hc2 QQ hQT, hs1 QQ h, one_smul, one_smul,
      zero_smul, zero_add, hYM, cT_add, cT_one, Matrix.map_add _ (map_add _), hone, Matrix.add_mul, Matrix.one_mul]
  have hPu : IsUnit (g + c • N) := by
    refine isUnit_matrix_of_resS hc _ fun QQ => ?_
    by_cases h : QQ ∈ T
    · rw [hPbar1 QQ h, Matrix.det_mul]
      refine mul_ne_zero (hgdet QQ) ?_
      exact ((Matrix.isUnit_iff_isUnit_det _).1 (y ⟨QQ, h⟩).isUnit).ne_zero
    · rw [hPbar2 QQ h]; exact hgdet QQ
  have hQu : IsUnit (g + sigS hc c • N) := by
    refine isUnit_matrix_of_resS hc _ fun QQ => ?_
    by_cases h : conjPl QQ ∈ T
    · rw [hQbar1 QQ h, Matrix.det_mul]
      refine mul_ne_zero ?_ (hgdet QQ)
      have e : ((cT (sigS hc) Y).map (resS F QQ)).det = resS F QQ (sigS hc Y.det) := by
        rw [← det_cT]
        exact (RingHom.map_det (resS F QQ) _).symm
      rw [e]
      intro h0
      have h1 := (resS_sigS_eq_zero_iff hc (isConjPl_conjPl QQ).symm _).1 h0
      rw [RingHom.map_det] at h1
      have h2 : ((resS F (conjPl QQ)).mapMatrix Y) = Y.map (resS F (conjPl QQ)) := rfl
      rw [h2, hY ⟨_, h⟩] at h1
      exact ((Matrix.isUnit_iff_isUnit_det _).1 (y ⟨conjPl QQ, h⟩).isUnit).ne_zero h1
    · rw [hQbar2 QQ h]; exact hgdet QQ
  obtain ⟨Pu, hPu'⟩ := hPu
  obtain ⟨Qu, hQu'⟩ := hQu
  refine ⟨G⁻¹ * Pu * Qu⁻¹ * G, unitary_of_herm (sigS hc) (sigS_sigS hc) G Pu Qu N c hGh hNh hPu' hQu', fun PP => ?_⟩
  rw [map_mul, map_mul, map_mul, map_inv, map_inv]
  have e1 : bc (resS F PP.1) Qu = bc (resS F PP.1) G := by
    apply Units.ext
    show (Qu : Matrix (Fin n) (Fin n) (intAf F E)).map (resS F PP.1) = g.map (resS F PP.1)
    rw [hQu', hQbar2 PP.1 (hsplit PP.1 PP.2)]
  have e2 : bc (resS F PP.1) Pu = bc (resS F PP.1) G * y PP := by
    apply Units.ext
    show (Pu : Matrix (Fin n) (Fin n) (intAf F E)).map (resS F PP.1) = g.map (resS F PP.1) * _
    rw [hPu', hPbar1 PP.1 PP.2]
  rw [e1, e2]
  group

end Surj

theorem reduction_surjective_bis : RedSurj := by
  intro F E _ _ _ _ _ _ hc n J L β T hU hβ hT y
  obtain ⟨G, hG⟩ := exists_gramS hc hU hβ
  obtain ⟨z, hz, hzy⟩ := exists_unitary_lift hc G (gramS_herm hc hU.herm hG) T hT y
  refine ⟨frGL β z, ⟨(frGL_mem_UA_iff hc hG z).2 hz, ⟨z, rfl⟩⟩, fun PP => ?_⟩
  rw [redFn_frGL]
  exact hzy PP

section Emb

variable {κ : Type} [CommRing κ] {r n : ℕ}

def rh_mat (A : Matrix (Fin r) (Fin r) κ) : Matrix (Fin n) (Fin n) κ :=
  fun i j => if h : i.val < r ∧ j.val < r then A ⟨i.val, h.1⟩ ⟨j.val, h.2⟩ else if i = j then 1 else 0

theorem rh_mat_lt (A : Matrix (Fin r) (Fin r) κ) {i j : Fin n} (hi : i.val < r) (hj : j.val < r) :
    rh_mat A i j = A ⟨i.val, hi⟩ ⟨j.val, hj⟩ := dif_pos ⟨hi, hj⟩

theorem rh_mat_ge_left (A : Matrix (Fin r) (Fin r) κ) {i j : Fin n} (hi : ¬ i.val < r) :
    rh_mat A i j = if i = j then 1 else 0 := dif_neg (fun h => hi h.1)

theorem rh_mat_ge_right (A : Matrix (Fin r) (Fin r) κ) {i j : Fin n} (hj : ¬ j.val < r) :
    rh_mat A i j = if i = j then 1 else 0 := dif_neg (fun h => hj h.2)

theorem rh_mat_one : (rh_mat (1 : Matrix (Fin r) (Fin r) κ) : Matrix (Fin n) (Fin n) κ) = 1 := by
  ext i j
  by_cases hi : i.val < r
  · by_cases hj : j.val < r
    · rw [rh_mat_lt _ hi hj, Matrix.one_apply, Matrix.one_apply]
      simp [Fin.ext_iff]
    · rw [rh_mat_ge_right _ hj, Matrix.one_apply]
  · rw [rh_mat_ge_left _ hi, Matrix.one_apply]

theorem rh_mat_mul (hr : r ≤ n) (A B : Matrix (Fin r) (Fin r) κ) :
    (rh_mat A : Matrix (Fin n) (Fin n) κ) * rh_mat B = rh_mat (A * B) := by
  ext i j
  rw [Matrix.mul_apply]
  by_cases hi : i.val < r
  · by_cases hj : j.val < r
    · rw [rh_mat_lt _ hi hj, Matrix.mul_apply]
      symm
      refine Fintype.sum_of_injective (Fin.castLE hr) (Fin.castLE_injective hr) _ _ (fun l hl => ?_) (fun l => ?_)
      · have hl' : ¬ l.val < r := fun h => hl ⟨⟨l.val, h⟩, by ext; rfl⟩
        have hil : i ≠ l := fun e => hl' (by rw [← e]; exact hi)
        rw [rh_mat_ge_right A hl', if_neg hil, zero_mul]
      · have hl : (Fin.castLE hr l).val < r := l.2
        exact (congrArg₂ (· * ·) (rh_mat_lt A hi hl) (rh_mat_lt B hl hj)).symm
    · have hij : i ≠ j := fun e => hj (by rw [← e]; exact hi)
      rw [rh_mat_ge_right _ hj, if_neg hij]
      refine Finset.sum_eq_zero fun l _ => ?_
      by_cases hl : l.val < r
      · have hlj : l ≠ j := fun e => hj (by rw [← e]; exact hl)
        rw [rh_mat_ge_right B hj, if_neg hlj, mul_zero]
      · have hil : i ≠ l := fun e => hl (by rw [← e]; exact hi)
        rw [rh_mat_ge_right A hl, if_neg hil, zero_mul]
  · rw [rh_mat_ge_left _ hi, Finset.sum_eq_single i]
    · rw [rh_mat_ge_left A hi, if_pos rfl, one_mul, rh_mat_ge_left B hi]
    · intro l _ hl
      rw [rh_mat_ge_left A hi, if_neg (Ne.symm hl), zero_mul]
    · intro h; exact absurd (Finset.mem_univ i) h

def rh_emb (hr : r ≤ n) : GL (Fin r) κ →* GL (Fin n) κ :=
  Units.map
    { toFun := fun A => (rh_mat A : Matrix (Fin n) (Fin n) κ)
      map_one' := rh_mat_one
      map_mul' := fun A B => (rh_mat_mul hr A B).symm }

theorem rh_emb_val (hr : r ≤ n) (y : GL (Fin r) κ) :
    ((rh_emb hr y : GL (Fin n) κ) : Matrix (Fin n) (Fin n) κ) = rh_mat (y : Matrix (Fin r) (Fin r) κ) := rfl

theorem rh_emb_mem (hr : r ≤ n) (y : GL (Fin r) κ) (b : Fin n → ℕ)
    (hb : ∀ i j : Fin n, i.val < r → j.val < r → b i = b j) : rh_emb hr y ∈ blockTri b := by
  refine mem_blockTri.2 fun i j hij => ?_
  rw [rh_emb_val]
  have h1 : ¬ (i.val < r ∧ j.val < r) := fun h => by
    rw [hb i j h.1 h.2] at hij; exact lt_irrefl _ hij
  have h2 : i ≠ j := fun e => by rw [e] at hij; exact lt_irrefl _ hij
  unfold rh_mat
  rw [dif_neg h1, if_neg h2]

theorem embed_mem_upper_block_triangular (hr : r ≤ n) (y : GL (Fin r) κ) : rh_emb hr y ∈ blockTri (blk2 (n := n) r) :=
  rh_emb_mem hr y _ fun i j hi hj => by simp [blk2, hi, hj]

theorem rh_emb_mem_blkOf (hr : r ≤ n) (t : ℕ) (y : GL (Fin r) κ) : rh_emb hr y ∈ blockTri (blkOf (n := n) r t) :=
  rh_emb_mem hr y _ fun i j hi hj => by simp [blkOf, hi, hj]

theorem upper_left_block_embed (hr : r ≤ n) (y : GL (Fin r) κ) : upperLeftBlock hr (rh_emb hr y) = y := by
  apply Units.ext
  rw [upper_block_val_submatrix hr (embed_mem_upper_block_triangular hr y), rh_emb_val]
  ext i j
  exact rh_mat_lt _ (show (Fin.castLE hr i).val < r from i.2) (show (Fin.castLE hr j).val < r from j.2)

end Emb

theorem rHomSurj_of (h : RedSurj) : RHomSurj := by
  classical
  intro F E _ _ _ _ _ _ hc LL _ n J L β D T hU hβ hg hq hT hdis y
  obtain ⟨x, hx, hred⟩ := h F E hc n J L β T hU hβ hT
    (fun PP => if hP : PP.1 ∈ D.Pg then rh_emb D.hr (y ⟨PP.1, hP⟩) else 1)
  have hred' : ∀ (PP : Pl E) (_ : PP ∈ T),
      redFn β PP x = if hP : PP ∈ D.Pg then rh_emb D.hr (y ⟨PP, hP⟩) else 1 := fun PP hP => hred ⟨PP, hP⟩
  have hpar : x ∈ parLev hc J β D := by
    refine mem_parLev.2 ⟨hx.1, hx.2, fun PP hP => ?_, fun PP hP => ?_⟩
    · rw [hred' PP (hg hP), dif_pos hP]
      exact rh_emb_mem_blkOf D.hr D.t _
    · have hn : PP ∉ D.Pg := Finset.disjoint_right.1 hdis hP
      rw [hred' PP (hq hP), dif_neg hn]
      exact Subgroup.one_mem _
  refine ⟨⟨x, hpar⟩, ?_⟩
  funext PP
  show upperLeftBlock D.hr (redFn β PP.1 x) = y PP
  rw [hred' PP.1 (hg PP.2), dif_pos PP.2]
  exact upper_left_block_embed D.hr _

theorem parahoric_reduction_surjective : RHomSurj := rHomSurj_of reduction_surjective_bis

section FrAlg

variable {R K : Type} [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K] [IsFractionRing R K]

theorem fr_li {S V V' V'' : Type} [CommRing S] [Algebra R S] [AddCommGroup V] [Module R V] [Module K V]
    [IsScalarTower R K V] [AddCommGroup V'] [Module R V'] [Module S V'] [IsScalarTower R S V'] [AddCommGroup V'']
    [Module R V''] (hRS : RingHom.ker (algebraMap R S) ≠ ⊤) (f : V'' →ₗ[R] V) (hf : Function.Injective f)
    (f' : V'' →ₗ[R] V') {ι : Type} {b : ι → V''} (hb' : LinearIndependent S (f' ∘ b)) :
    LinearIndependent K (f ∘ b) := by
  contrapose hb' with hb
  simp only [linearIndependent_iff', not_forall] at hb ⊢
  obtain ⟨s, g, eq, j', hj's, hj'g⟩ := hb
  use s
  obtain ⟨a, hag, j, hjs, hgI⟩ := Ideal.exist_integer_multiples_notMem hRS s g hj's hj'g
  choose g'' hg'' using hag
  let := Classical.propDecidable
  let g' i := if h : i ∈ s then g'' i h else 0
  have hg' : ∀ i ∈ s, algebraMap _ _ (g' i) = a * g i := by
    intro i hi; exact (congr_arg _ (dif_pos hi)).trans (hg'' i hi)
  have hgI : algebraMap R S (g' j) ≠ 0 := by
    simp only [FractionalIdeal.mem_coeIdeal, not_exists, not_and'] at hgI
    exact hgI _ (hg' j hjs)
  refine ⟨fun i => algebraMap R S (g' i), ?_, j, hjs, hgI⟩
  have eq : f (∑ i ∈ s, g' i • b i) = 0 := by
    rw [map_sum, ← smul_zero a, ← eq, Finset.smul_sum]
    refine Finset.sum_congr rfl ?_
    intro i hi
    rw [map_smul, ← IsScalarTower.algebraMap_smul K, hg' i hi, ← smul_assoc,
      smul_eq_mul, Function.comp_apply]
  simp only [IsScalarTower.algebraMap_smul, ← map_smul, ← map_sum,
    (f.map_eq_zero_iff hf).mp eq, map_zero, (· ∘ ·)]

theorem fr_gen_mod (P : Ideal R) [hP : P.IsMaximal] {n : ℕ} (L : Submodule R (Fin n → K)) (hfg : L.FG) :
    ∃ g : Fin n → (Fin n → K), (∀ i, g i ∈ L) ∧ L ≤ Submodule.span R (Set.range g) ⊔ P • L := by
  classical
  let _ : Field (R ⧸ P) := Ideal.Quotient.field P
  have : Module.Finite R ↥L := Module.Finite.iff_fg.2 hfg
  have : Module.Finite (R ⧸ P) (↥L ⧸ (P • (⊤ : Submodule R ↥L))) :=
    Module.Finite.of_restrictScalars_finite R (R ⧸ P) _
  let c := Module.finBasis (R ⧸ P) (↥L ⧸ (P • (⊤ : Submodule R ↥L)))
  choose lift hlift using Submodule.mkQ_surjective (P • (⊤ : Submodule R ↥L))
  let ct : Fin (Module.finrank (R ⧸ P) (↥L ⧸ (P • (⊤ : Submodule R ↥L)))) → ↥L := fun i => lift (c i)
  have hli : LinearIndependent K (L.subtype ∘ ct) := by
    refine fr_li (S := R ⧸ P) ?_ L.subtype (Submodule.subtype_injective L)
      (Submodule.mkQ (P • (⊤ : Submodule R ↥L))) ?_
    · rw [Ideal.Quotient.algebraMap_eq, Ideal.mk_ker]; exact hP.ne_top
    · have : (Submodule.mkQ (P • (⊤ : Submodule R ↥L))) ∘ ct = c := funext fun i => hlift _
      rw [this]; exact c.linearIndependent
  have hmn : Module.finrank (R ⧸ P) (↥L ⧸ (P • (⊤ : Submodule R ↥L))) ≤ n := by
    have := hli.fintype_card_le_finrank
    simpa using this
  refine ⟨fun i => if h : i.val < Module.finrank (R ⧸ P) (↥L ⧸ (P • (⊤ : Submodule R ↥L))) then
    (ct ⟨i.val, h⟩ : Fin n → K) else 0, ?_, ?_⟩
  · intro i
    dsimp only
    split_ifs
    · exact (ct _).2
    · exact L.zero_mem
  · intro x hx
    choose r hr using fun j => Ideal.Quotient.mk_surjective
      (c.repr (Submodule.mkQ (P • (⊤ : Submodule R ↥L)) ⟨x, hx⟩) j)
    have hdiff : (⟨x, hx⟩ : ↥L) - ∑ j, r j • ct j ∈ P • (⊤ : Submodule R ↥L) := by
      rw [← Submodule.Quotient.mk_eq_zero, Submodule.Quotient.mk_sub, sub_eq_zero]
      have h1 := c.sum_repr (Submodule.mkQ (P • (⊤ : Submodule R ↥L)) ⟨x, hx⟩)
      show Submodule.mkQ (P • (⊤ : Submodule R ↥L)) ⟨x, hx⟩ =
        Submodule.mkQ (P • (⊤ : Submodule R ↥L)) (∑ j, r j • ct j)
      conv_lhs => rw [← h1]
      rw [map_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [← hr j, map_smul, hlift]
      rfl
    have hdiff' : x - ∑ j, r j • (ct j : Fin n → K) ∈ P • L := by
      have h2 := Submodule.mem_map_of_mem (f := L.subtype) hdiff
      rw [Submodule.map_smul'', Submodule.map_subtype_top] at h2
      simpa using h2
    have hx2 : x = ∑ j, r j • (ct j : Fin n → K) + (x - ∑ j, r j • (ct j : Fin n → K)) := by abel
    rw [hx2]
    refine Submodule.add_mem_sup (Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ ?_) hdiff'
    refine Submodule.subset_span ⟨⟨j.val, lt_of_lt_of_le j.2 hmn⟩, ?_⟩
    dsimp only
    rw [dif_pos j.2]

end FrAlg

section FrNF

variable {E : Type} [Field E] [NumberField E] {n : ℕ}

theorem fr_coprime (I : Ideal (𝓞 E)) (hI : I ≠ ⊥) (D : ℕ) (h : I ⊔ Ideal.span {(D : 𝓞 E)} = ⊤) :
    Nat.Coprime (Ideal.absNorm I) D := by
  classical
  by_contra hc
  obtain ⟨p, hp, h1, h2⟩ := Nat.Prime.not_coprime_iff_dvd.1 hc
  have := Fact.mk hp
  have : Finite (𝓞 E ⧸ I) := Ideal.finiteQuotientOfFreeOfNeBot I hI
  have := Fintype.ofFinite (𝓞 E ⧸ I)
  have hcard : p ∣ Fintype.card (𝓞 E ⧸ I) := by
    rw [← Nat.card_eq_fintype_card]; exact h1
  obtain ⟨x, hx⟩ := exists_prime_addOrderOf_dvd_card p hcard
  have hpx : p • x = 0 := by rw [← hx]; exact addOrderOf_nsmul_eq_zero x
  have hx0 : x ≠ 0 := by
    rintro rfl
    rw [addOrderOf_zero] at hx
    exact hp.one_lt.ne hx
  obtain ⟨q, rfl⟩ := h2
  have h1' : (1 : 𝓞 E) ∈ I ⊔ Ideal.span {((p * q : ℕ) : 𝓞 E)} := by rw [h]; exact Submodule.mem_top
  obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.1 h1'
  obtain ⟨t, rfl⟩ := Ideal.mem_span_singleton'.1 hb
  apply hx0
  have e1 : Ideal.Quotient.mk I (t * ((p * q : ℕ) : 𝓞 E)) = 1 := by
    rw [← map_one (Ideal.Quotient.mk I), ← hab, map_add, Ideal.Quotient.eq_zero_iff_mem.2 ha, zero_add]
  calc x = Ideal.Quotient.mk I (t * ((p * q : ℕ) : 𝓞 E)) * x := by rw [e1, one_mul]
    _ = Ideal.Quotient.mk I t * (Ideal.Quotient.mk I (q : 𝓞 E)) * (p • x) := by
        rw [nsmul_eq_mul]; push_cast; simp only [map_mul, map_natCast]; ring
    _ = 0 := by rw [hpx, mul_zero]

theorem fr_good_basis (L : Submodule (𝓞 E) (Fin n → E)) (hfg : L.FG) (D : ℕ) (hD : D ≠ 0) (P0 : Pl E)
    (hP0 : (D : 𝓞 E) ∈ P0.asIdeal) :
    ∃ (b : Fin n → (Fin n → E)) (d : ℕ), (∀ i, b i ∈ L) ∧ d ≠ 0 ∧ Nat.Coprime d D ∧
      ∀ x ∈ L, (d : 𝓞 E) • x ∈ Submodule.span (𝓞 E) (Set.range b) := by
  classical
  have hD' : (D : 𝓞 E) ≠ 0 := Nat.cast_ne_zero.2 hD
  set Ps : Finset (Pl E) := primesOf (D : 𝓞 E) with hPs
  have hg : ∀ PP : Pl E, ∃ g : Fin n → (Fin n → E), (∀ i, g i ∈ L) ∧
      L ≤ Submodule.span (𝓞 E) (Set.range g) ⊔ PP.asIdeal • L := fun PP => by
    have := PP.isMaximal
    exact fr_gen_mod PP.asIdeal L hfg
  choose g hgL hgen using hg
  have hε : ∀ PP : Pl E, PP ∈ Ps → ∃ ε : 𝓞 E, ε - 1 ∈ PP.asIdeal ∧ ∀ QQ ∈ Ps, QQ ≠ PP → ε ∈ QQ.asIdeal := by
    intro PP hPP
    obtain ⟨y, hy⟩ := IsDedekindDomain.exists_forall_sub_mem_ideal (s := Ps) (fun QQ : Pl E => QQ.asIdeal)
      (fun _ => 1) (fun QQ _ => QQ.prime) (fun i _ j _ hij h => hij (HeightOneSpectrum.ext h))
      (fun QQ => if QQ.1 = PP then 1 else 0)
    refine ⟨y, ?_, ?_⟩
    · have := hy PP hPP
      simpa using this
    · intro QQ hQ hne
      have := hy QQ hQ
      simpa [hne] using this
  choose! ε hε1 hε0 using hε
  let b : Fin n → (Fin n → E) := fun i => ∑ PP ∈ Ps, ε PP • g PP i
  set N := Submodule.span (𝓞 E) (Set.range b) with hN
  have hbL : ∀ i, b i ∈ L := fun i => Submodule.sum_mem _ fun PP _ => L.smul_mem _ (hgL PP i)
  have hsup : ∀ PP ∈ Ps, L ≤ N ⊔ PP.asIdeal • L := by
    intro PP hPP
    refine le_trans (hgen PP) (sup_le ?_ le_sup_right)
    rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    have e : g PP i = b i - ((ε PP - 1) • g PP i + ∑ QQ ∈ Ps.erase PP, ε QQ • g QQ i) := by
      show _ = (∑ QQ ∈ Ps, ε QQ • g QQ i) - _
      rw [← Finset.add_sum_erase _ _ hPP, sub_smul, one_smul]; abel
    rw [SetLike.mem_coe, e]
    refine Submodule.sub_mem _ (Submodule.mem_sup_left (Submodule.subset_span ⟨i, rfl⟩))
      (Submodule.mem_sup_right ?_)
    refine Submodule.add_mem _ (Submodule.smul_mem_smul (hε1 PP hPP) (hgL PP i))
      (Submodule.sum_mem _ fun QQ hQ => ?_)
    exact Submodule.smul_mem_smul
      (hε0 QQ (Finset.mem_of_mem_erase hQ) PP hPP (Finset.ne_of_mem_erase hQ).symm) (hgL QQ i)
  have hr : ∀ PP ∈ Ps, ∃ r : 𝓞 E, r - 1 ∈ PP.asIdeal ∧ ∀ x ∈ L, r • x ∈ N := by
    intro PP hPP
    obtain ⟨r, hr1, hr2⟩ := Submodule.exists_sub_one_mem_and_smul_le_of_fg_of_le_sup hfg le_rfl (hsup PP hPP)
    exact ⟨r, hr1, fun x hx => hr2 (Submodule.smul_mem_pointwise_smul x r L hx)⟩
  let cI : Ideal (𝓞 E) :=
    { carrier := {r | ∀ x ∈ L, r • x ∈ N}
      add_mem' := fun {a b} ha hb x hx => by rw [add_smul]; exact N.add_mem (ha x hx) (hb x hx)
      zero_mem' := fun x _ => by rw [zero_smul]; exact N.zero_mem
      smul_mem' := fun c {a} ha x hx => by rw [smul_eq_mul, mul_smul]; exact N.smul_mem _ (ha x hx) }
  have hP0' : P0 ∈ Ps := mem_primesOf.2 ⟨hD', hP0⟩
  have hcI0 : cI ≠ ⊥ := by
    obtain ⟨r, hr1, hr2⟩ := hr P0 hP0'
    intro h0
    have h1 : r ∈ cI := hr2
    rw [h0, Ideal.mem_bot] at h1
    rw [h1, zero_sub, neg_mem_iff] at hr1
    exact P0.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 hr1)
  have htop : cI ⊔ Ideal.span {(D : 𝓞 E)} = ⊤ := by
    by_contra hne
    obtain ⟨mI, hmax, hle⟩ := Ideal.exists_le_maximal _ hne
    have hDm : (D : 𝓞 E) ∈ mI := hle (Submodule.mem_sup_right (Ideal.mem_span_singleton_self _))
    let PP : Pl E := ⟨mI, hmax.isPrime, fun h => hD' (by rw [h] at hDm; exact hDm)⟩
    obtain ⟨r, hr1, hr2⟩ := hr PP (mem_primesOf.2 ⟨hD', hDm⟩)
    have h1 : r ∈ mI := hle (Submodule.mem_sup_left hr2)
    have h2 : (1 : 𝓞 E) ∈ mI := by
      have := mI.sub_mem h1 hr1
      simpa using this
    exact hmax.ne_top ((Ideal.eq_top_iff_one _).2 h2)
  exact ⟨b, Ideal.absNorm cI, hbL, fun h => hcI0 (Ideal.absNorm_eq_zero_iff.1 h), fr_coprime cI hcI0 D htop,
    Ideal.absNorm_mem cI⟩

end FrNF

section FrAd

variable {F : Type} [Field F] [NumberField F]

theorem fr_inv_int (v : HeightOneSpectrum (𝓞 F)) (r : 𝓞 F) (hr : r ∉ v.asIdeal) :
    (algebraMap (𝓞 F) (v.adicCompletion F) r)⁻¹ ∈ v.adicCompletionIntegers F := by
  rw [HeightOneSpectrum.mem_adicCompletionIntegers, map_inv₀, Formalism.UG.P.csApprox_val_int,
    HeightOneSpectrum.intValuation_eq_one_iff.2 hr, inv_one]

theorem fr_adele (D d : 𝓞 F) (hD : D ≠ 0)
    (hcop : ∀ v : HeightOneSpectrum (𝓞 F), D ∈ v.asIdeal → d ∉ v.asIdeal) :
    ∃ e w w' : Af F, e ∈ intAd F ∧ w ∈ intAd F ∧ w' ∈ intAd F ∧ e * e = e ∧ e * w' = 0 ∧
      algebraMap (𝓞 F) (Af F) d * w = e ∧ algebraMap (𝓞 F) (Af F) D * w' = 1 - e := by
  classical
  have he : ∀ v : HeightOneSpectrum (𝓞 F),
      (if D ∈ v.asIdeal then (1 : v.adicCompletion F) else 0) ∈ v.adicCompletionIntegers F := by
    intro v
    split_ifs
    · exact one_mem _
    · exact zero_mem _
  have hw : ∀ v : HeightOneSpectrum (𝓞 F),
      (if D ∈ v.asIdeal then (algebraMap (𝓞 F) (v.adicCompletion F) d)⁻¹ else 0) ∈
        v.adicCompletionIntegers F := by
    intro v
    split_ifs with h
    · exact fr_inv_int v d (hcop v h)
    · exact zero_mem _
  have hw' : ∀ v : HeightOneSpectrum (𝓞 F),
      (if D ∈ v.asIdeal then 0 else (algebraMap (𝓞 F) (v.adicCompletion F) D)⁻¹) ∈
        v.adicCompletionIntegers F := by
    intro v
    split_ifs with h
    · exact zero_mem _
    · exact fr_inv_int v D h
  refine ⟨⟨fun v => if D ∈ v.asIdeal then (1 : v.adicCompletion F) else 0, Filter.Eventually.of_forall he⟩,
    ⟨fun v => if D ∈ v.asIdeal then (algebraMap (𝓞 F) (v.adicCompletion F) d)⁻¹ else 0,
      Filter.Eventually.of_forall hw⟩,
    ⟨fun v => if D ∈ v.asIdeal then 0 else (algebraMap (𝓞 F) (v.adicCompletion F) D)⁻¹,
      Filter.Eventually.of_forall hw'⟩, he, hw, hw', ?_, ?_, ?_, ?_⟩
  · ext1 v
    show (if D ∈ v.asIdeal then (1 : v.adicCompletion F) else 0) * (if D ∈ v.asIdeal then 1 else 0) =
      if D ∈ v.asIdeal then 1 else 0
    split_ifs <;> simp
  · ext1 v
    show (if D ∈ v.asIdeal then (1 : v.adicCompletion F) else 0) *
      (if D ∈ v.asIdeal then 0 else (algebraMap (𝓞 F) (v.adicCompletion F) D)⁻¹) = 0
    split_ifs <;> simp
  · ext1 v
    show algebraMap (𝓞 F) (v.adicCompletion F) d *
      (if D ∈ v.asIdeal then (algebraMap (𝓞 F) (v.adicCompletion F) d)⁻¹ else 0) =
      if D ∈ v.asIdeal then 1 else 0
    split_ifs with h
    · refine mul_inv_cancel₀ (Formalism.UG.P.levelaf_algebraMap_ne_zero v d ?_)
      rintro rfl
      exact hcop v h (Ideal.zero_mem _)
    · rw [mul_zero]
  · ext1 v
    show algebraMap (𝓞 F) (v.adicCompletion F) D *
      (if D ∈ v.asIdeal then 0 else (algebraMap (𝓞 F) (v.adicCompletion F) D)⁻¹) =
      1 - if D ∈ v.asIdeal then 1 else 0
    split_ifs with h
    · rw [mul_zero, sub_self]
    · rw [sub_zero]
      exact mul_inv_cancel₀ (Formalism.UG.P.levelaf_algebraMap_ne_zero v D hD)

end FrAd

section FrGlue

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}

local notation "𝒜" => E ⊗[F] Af F
local notation "ιA" => inclE (F := F) (E := E) (Af F)

theorem fr_mem_hat {L : Submodule (𝓞 E) (Fin n → E)} {l : Fin n → E} (hl : l ∈ L) :
    (fun i => ιA (l i)) ∈ hatL (F := F) L :=
  Submodule.subset_span ⟨l, hl, rfl⟩

theorem fr_glue (L : Submodule (𝓞 E) (Fin n → E)) (B C : Matrix (Fin n) (Fin n) E) (hBC : B * C = 1)
    (hB : ∀ j, (fun i => B i j) ∈ L) (ε ω κ γ : 𝒜) (hε : ε ∈ intAf F E) (hω : ω ∈ intAf F E)
    (hidem : ε * ε = ε) (hεκ : ε * κ = 0) (hκγ : κ * γ = 1 - ε) (d : 𝓞 E)
    (hdω : ιA (algebraMap (𝓞 E) E d) * ω = ε)
    (hdL : ∀ x ∈ L, ∃ a : Fin n → 𝓞 E, d • x = B *ᵥ (fun j => algebraMap (𝓞 E) E (a j)))
    (hlow : ∀ v : Fin n → 𝒜, (∀ i, v i ∈ intAf F E) → (fun i => γ * v i) ∈ hatL (F := F) L)
    (hup : ∀ v ∈ hatL (F := F) L, ∀ i, κ * v i ∈ intAf F E) :
    ∃ β : GL (Fin n) 𝒜, IsFrame β L := by
  have hCB : C * B = 1 := mul_eq_one_comm.1 hBC
  set B' : Matrix (Fin n) (Fin n) 𝒜 := B.map ιA with hB'
  set C' : Matrix (Fin n) (Fin n) 𝒜 := C.map ιA with hC'
  have hBC' : B' * C' = 1 := by
    rw [hB', hC', ← Matrix.map_mul, hBC, Matrix.map_one _ (map_zero _) (map_one _)]
  have hs3 : (1 - ε) * γ * ε = 0 := by
    have : (1 - ε) * γ * ε = γ * (ε - ε * ε) := by ring
    rw [this, hidem, sub_self, mul_zero]
  have hs4 : (1 - ε) * γ * κ = 1 - ε := by
    have : (1 - ε) * γ * κ = (1 - ε) * (κ * γ) := by ring
    rw [this, hκγ]
    linear_combination hidem
  have h1 : (ε • B' + ((1 - ε) * γ) • (1 : Matrix (Fin n) (Fin n) 𝒜)) *
      (ε • C' + κ • (1 : Matrix (Fin n) (Fin n) 𝒜)) = 1 := by
    simp only [add_mul, mul_add, Matrix.smul_mul, Matrix.mul_smul, smul_smul, Matrix.mul_one, Matrix.one_mul]
    rw [hidem, mul_comm ε ((1 - ε) * γ), hs3, mul_comm κ ε, hεκ, mul_comm κ ((1 - ε) * γ), hs4, hBC', zero_smul,
      zero_smul, add_zero, zero_add, ← add_smul, add_sub_cancel, one_smul]
  have h2 := mul_eq_one_comm.1 h1
  have hinv : ∀ (x : Fin n → 𝒜) (i : Fin n),
      ((ε • C' + κ • (1 : Matrix (Fin n) (Fin n) 𝒜)) *ᵥ x) i = ε * (C' *ᵥ x) i + κ * x i := by
    intro x i
    rw [Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec]
    rfl
  have key1 : ∀ x ∈ hatL (F := F) L, ∀ i, ε * (C' *ᵥ x) i ∈ intAf F E := by
    intro x hx
    unfold hatL latS at hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨l, hl, rfl⟩ := hx
      intro i
      obtain ⟨a, ha⟩ := hdL l hl
      have e1 : (C' *ᵥ fun i => ιA (l i)) i = ιA ((C *ᵥ l) i) := by
        simp only [Matrix.mulVec, dotProduct, hC', Matrix.map_apply, map_sum, map_mul]
      have e2 : algebraMap (𝓞 E) E d * (C *ᵥ l) i = algebraMap (𝓞 E) E (a i) := by
        have h3 : C *ᵥ (d • l) = fun j => algebraMap (𝓞 E) E (a j) := by
          rw [ha, Matrix.mulVec_mulVec, hCB, Matrix.one_mulVec]
        have h4 := congrFun h3 i
        rw [Matrix.mulVec_smul, Pi.smul_apply, Algebra.smul_def] at h4
        exact h4
      rw [e1, ← hdω, mul_right_comm, ← map_mul, e2]
      exact mul_mem (Formalism.UG.CS.incl_int (a i)) hω
    | zero =>
      intro i
      rw [Matrix.mulVec_zero, Pi.zero_apply, mul_zero]
      exact zero_mem _
    | add x y _ _ hx hy =>
      intro i
      rw [Matrix.mulVec_add, Pi.add_apply, mul_add]
      exact add_mem (hx i) (hy i)
    | smul s x _ hx =>
      intro i
      have e : (C' *ᵥ (s • x)) i = (s : 𝒜) * (C' *ᵥ x) i := by
        rw [Matrix.mulVec_smul]; rfl
      rw [e, mul_left_comm]
      exact mul_mem s.2 (hx i)
  refine ⟨⟨_, _, h1, h2⟩, fun x => ?_⟩
  show x ∈ hatL (F := F) L ↔ ∀ i, ((ε • C' + κ • (1 : Matrix (Fin n) (Fin n) 𝒜)) *ᵥ x) i ∈ intAf F E
  constructor
  · intro hx i
    rw [hinv]
    exact add_mem (key1 x hx i) (hup x hx i)
  · intro hy
    set y := (ε • C' + κ • (1 : Matrix (Fin n) (Fin n) 𝒜)) *ᵥ x with hydef
    have hxy : x = (ε • B' + ((1 - ε) * γ) • (1 : Matrix (Fin n) (Fin n) 𝒜)) *ᵥ y := by
      rw [hydef, Matrix.mulVec_mulVec, h1, Matrix.one_mulVec]
    have e3 : (ε • B' + ((1 - ε) * γ) • (1 : Matrix (Fin n) (Fin n) 𝒜)) *ᵥ y =
        (⟨ε, hε⟩ : intAf F E) • (∑ j, (⟨y j, hy j⟩ : intAf F E) • (fun i => ιA (B i j))) +
          (⟨1 - ε, sub_mem (one_mem _) hε⟩ : intAf F E) • (fun i => γ * y i) := by
      funext i
      rw [Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec]
      simp only [Pi.add_apply, Pi.smul_apply, Finset.sum_apply, Subring.smul_def, smul_eq_mul, Matrix.mulVec,
        dotProduct, hB', Matrix.map_apply]
      congr 1
      · congr 1
        exact Finset.sum_congr rfl fun j _ => mul_comm _ _
      · ring
    rw [hxy, e3]
    exact Submodule.add_mem _ (Submodule.smul_mem _ _ (Submodule.sum_mem _ fun j _ =>
      Submodule.smul_mem _ _ (fr_mem_hat (hB j)))) (Submodule.smul_mem _ _ (hlow y hy))

end FrGlue

theorem frame_exists_alt : FrameExists := by
  classical
  intro F E _ _ _ _ _ n L hL
  have hfin : Module.Finite (𝓞 E) L := Module.Finite.iff_fg.2 hL.fg
  have hspan := hL.span_eq_top
  obtain ⟨c, hc0, hc⟩ := Formalism.UG.P.adelstabL_lower (F := F) L hspan
  obtain ⟨d0, hd00, hd0⟩ := Formalism.UG.P.adelstabL_upper (F := F) L hfin
  obtain ⟨p, hp0, hp⟩ := Ring.not_isField_iff_exists_prime.1 (RingOfIntegers.not_isField E)
  let P0 : Pl E := ⟨p, hp, hp0⟩
  set D1 : ℕ := Ideal.absNorm (Ideal.span {c * d0} : Ideal (𝓞 F)) with hD1
  set D2 : ℕ := Ideal.absNorm P0.asIdeal with hD2
  have hD1' : D1 ≠ 0 := by
    rw [hD1, Ne, Ideal.absNorm_eq_zero_iff, Ideal.span_singleton_eq_bot]
    exact mul_ne_zero hc0 hd00
  have hD2' : D2 ≠ 0 := by
    rw [hD2, Ne, Ideal.absNorm_eq_zero_iff]
    exact hp0
  obtain ⟨t, ht⟩ : ∃ t : 𝓞 F, t * (c * d0) = (D1 : 𝓞 F) :=
    Ideal.mem_span_singleton'.1 (Ideal.absNorm_mem _)
  have hP0 : ((D1 * D2 : ℕ) : 𝓞 E) ∈ P0.asIdeal := by
    rw [Nat.cast_mul]
    exact Ideal.mul_mem_left _ _ (Ideal.absNorm_mem _)
  obtain ⟨b, d, hbL, hd, hcop, hdL⟩ := fr_good_basis L hL.fg (D1 * D2) (mul_ne_zero hD1' hD2') P0 hP0
  have hcopF : ∀ v : HeightOneSpectrum (𝓞 F), ((D1 * D2 : ℕ) : 𝓞 F) ∈ v.asIdeal →
      ((d : ℕ) : 𝓞 F) ∉ v.asIdeal := by
    intro v h1 h2
    obtain ⟨x, y, hxy⟩ := Nat.isCoprime_iff_coprime.2 hcop
    have h3 : (1 : 𝓞 F) ∈ v.asIdeal := by
      have e : (1 : 𝓞 F) = (x : 𝓞 F) * ((d : ℕ) : 𝓞 F) + (y : 𝓞 F) * ((D1 * D2 : ℕ) : 𝓞 F) := by
        have := congrArg (Int.cast : ℤ → 𝓞 F) hxy
        push_cast at this ⊢
        exact this.symm
      rw [e]
      exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ h2) (Ideal.mul_mem_left _ _ h1)
    exact v.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 h3)
  obtain ⟨e, w, w', he, hw, hw', hee, hew', hdw, hDw'⟩ := fr_adele ((D1 * D2 : ℕ) : 𝓞 F) ((d : ℕ) : 𝓞 F)
    (Nat.cast_ne_zero.2 (mul_ne_zero hD1' hD2')) hcopF
  have hdE : (d : E) ≠ 0 := Nat.cast_ne_zero.2 hd
  have hspanb : Submodule.span E (Set.range b) = ⊤ := by
    rw [eq_top_iff, ← hspan, Submodule.span_le]
    intro x hx
    have h2 : ((d : ℕ) : 𝓞 E) • x ∈ Submodule.span E (Set.range b) :=
      Submodule.span_subset_span (𝓞 E) E _ (hdL x hx)
    have h3 : x = ((d : E))⁻¹ • (((d : ℕ) : 𝓞 E) • x) := by
      rw [← algebraMap_smul E (((d : ℕ) : 𝓞 E)) x, map_natCast, inv_smul_smul₀ hdE]
    rw [SetLike.mem_coe, h3]
    exact Submodule.smul_mem _ _ h2
  choose Cc hCc using fun k : Fin n => (Submodule.mem_span_range_iff_exists_fun E).1
    (hspanb ▸ Submodule.mem_top : (Pi.single k 1 : Fin n → E) ∈ Submodule.span E (Set.range b))
  have hBC : (Matrix.of fun i j => b j i : Matrix (Fin n) (Fin n) E) * (Matrix.of fun j k => Cc k j) = 1 := by
    ext i k
    have h1 := congrFun (hCc k) i
    rw [Finset.sum_apply] at h1
    rw [Matrix.mul_apply, Matrix.one_apply, ← Pi.single_apply, ← h1]
    exact Finset.sum_congr rfl fun j _ => mul_comm _ _
  have hmem : ∀ {a : Af F}, a ∈ intAd F → ((1 : E) ⊗ₜ[F] a : E ⊗[F] Af F) ∈ intAf F E :=
    fun {a} ha => Subring.subset_closure (Or.inr ⟨⟨a, ha⟩, rfl⟩)
  have hDeq : t * d0 * (D2 : 𝓞 F) * c = ((D1 * D2 : ℕ) : 𝓞 F) := by
    rw [Nat.cast_mul, ← ht]; ring
  refine fr_glue L _ _ hBC (fun j => hbL j) ((1 : E) ⊗ₜ[F] e) ((1 : E) ⊗ₜ[F] w)
    (((1 : E) ⊗ₜ[F] w') * Formalism.UG.P.levelafC E (t * d0 * (D2 : 𝓞 F))) (Formalism.UG.P.levelafC E c) (hmem he) (hmem hw)
    ?_ ?_ ?_ ((d : ℕ) : 𝓞 E) ?_ ?_ hc ?_
  · rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul, hee]
  · rw [← mul_assoc, Algebra.TensorProduct.tmul_mul_tmul, hew', TensorProduct.tmul_zero, zero_mul]
  · rw [mul_assoc, ← Formalism.UG.P.levelafC_mul, hDeq]
    unfold Formalism.UG.P.levelafC
    rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_comm w', hDw', TensorProduct.tmul_sub]
    rfl
  · have h1 : inclE (F := F) (E := E) (Af F) (algebraMap (𝓞 E) E ((d : ℕ) : 𝓞 E)) =
        Formalism.UG.P.levelafC E ((d : ℕ) : 𝓞 F) := by
      rw [levelafC_eq_incl]
      simp only [map_natCast]
    rw [h1]
    unfold Formalism.UG.P.levelafC
    rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul, hdw]
  · intro x hx
    obtain ⟨a, ha⟩ := (Submodule.mem_span_range_iff_exists_fun (𝓞 E)).1 (hdL x hx)
    refine ⟨a, ?_⟩
    rw [← ha]
    funext i
    rw [Finset.sum_apply]
    simp only [Matrix.mulVec, dotProduct, Matrix.of_apply, Pi.smul_apply, Algebra.smul_def]
    exact Finset.sum_congr rfl fun j _ => mul_comm _ _
  · intro v hv i
    have e1 : ((1 : E) ⊗ₜ[F] w') * Formalism.UG.P.levelafC E (t * d0 * (D2 : 𝓞 F)) * v i =
        ((1 : E) ⊗ₜ[F] w') * Formalism.UG.P.levelafC E (t * (D2 : 𝓞 F)) * (Formalism.UG.P.levelafC E d0 * v i) := by
      rw [show t * d0 * (D2 : 𝓞 F) = t * (D2 : 𝓞 F) * d0 by ring, Formalism.UG.P.levelafC_mul]
      ring
    rw [e1]
    exact mul_mem (mul_mem (hmem hw') (Formalism.UG.P.levelafC_mem _)) (hd0 v hv i)

theorem minkNum_eq_minkowskiM (N : ℕ) : minkNum N = Formalism.HermitianLatticeCounting.S6.minkowskiM N := rfl

theorem minkNum_eq_minkM (N : ℕ) : minkNum N = Formalism.BasicNotions.minkM N := rfl

theorem minkNum_dvd {a b : ℕ} (h : a ≤ b) : minkNum a ∣ minkNum b := Formalism.BasicNotions.minkM_dvd_minkM h

theorem cm_finrank {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]
    (hc : CMData F E) : Module.finrank ℚ E = 2 * Module.finrank ℚ F := by
  rw [← Module.finrank_mul_finrank ℚ F E, hc.deg2, mul_comm]

section Lat

variable {E : Type} [Field E] [NumberField E] {n : ℕ}

theorem mk_span_rat (Λ : Submodule (𝓞 E) (Fin n → E)) (hΛ : Submodule.span E (Λ : Set (Fin n → E)) = ⊤) :
    Submodule.span ℚ ((Λ.restrictScalars ℤ : Submodule ℤ (Fin n → E)) : Set (Fin n → E)) = ⊤ := by
  have hsm : ∀ (e : E) (y : Fin n → E), y ∈ Submodule.span ℚ (Λ : Set (Fin n → E)) →
      e • y ∈ Submodule.span ℚ (Λ : Set (Fin n → E)) := by
    intro e y hy
    obtain ⟨m, hm0, hm⟩ := Formalism.UG.P.adelstabL_den (E := E) (fun _ : Fin 1 => e)
    have hm1 := hm 0
    induction hy using Submodule.span_induction with
    | mem l hl =>
      have h1 : (⟨(m : E) * e, hm1⟩ : 𝓞 E) • l ∈ Λ := Λ.smul_mem _ hl
      have h2 : e • l = ((m : ℚ)⁻¹) • ((⟨(m : E) * e, hm1⟩ : 𝓞 E) • l) := by
        funext i
        have hmE : (m : E) ≠ 0 := by exact_mod_cast hm0
        show e * l i = ((m : ℚ)⁻¹) • (((m : E) * e) * l i)
        rw [Algebra.smul_def, map_inv₀]
        have : (algebraMap ℚ E) (m : ℚ) = (m : E) := by simp
        rw [this]
        field_simp
      rw [h2]
      exact Submodule.smul_mem _ _ (Submodule.subset_span h1)
    | zero => rw [smul_zero]; exact Submodule.zero_mem _
    | add a b _ _ ha hb => rw [smul_add]; exact Submodule.add_mem _ ha hb
    | smul q a _ ha => rw [smul_comm]; exact Submodule.smul_mem _ _ ha
  have key : ∀ x ∈ Submodule.span E (Λ : Set (Fin n → E)), x ∈ Submodule.span ℚ (Λ : Set (Fin n → E)) := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem l hl => exact Submodule.subset_span hl
    | zero => exact Submodule.zero_mem _
    | add a b _ _ ha hb => exact Submodule.add_mem _ ha hb
    | smul e a _ ha => exact hsm e a ha
  exact eq_top_iff.2 fun x _ => key x (by rw [hΛ]; trivial)

theorem mk_isLattice (Λ : Submodule (𝓞 E) (Fin n → E)) (hΛ : Submodule.IsLattice E Λ) :
    Submodule.IsLattice ℚ (Λ.restrictScalars ℤ : Submodule ℤ (Fin n → E)) :=
  ⟨hΛ.fg.restrictScalars, mk_span_rat Λ hΛ.span_eq_top⟩

theorem mk_finrank (Λ : Submodule (𝓞 E) (Fin n → E)) (hΛ : Submodule.IsLattice E Λ) :
    Module.finrank ℤ (Λ.restrictScalars ℤ : Submodule ℤ (Fin n → E)) = Module.finrank ℚ E * n := by
  have := mk_isLattice Λ hΛ
  have h1 : Module.finrank ℤ (Λ.restrictScalars ℤ : Submodule ℤ (Fin n → E)) = Module.finrank ℚ (Fin n → E) :=
    Module.finrank_eq_of_rank_eq (by
      rw [Submodule.IsLattice.rank' ℚ (Λ.restrictScalars ℤ : Submodule ℤ (Fin n → E))]
      exact (Module.finrank_eq_rank ℚ (Fin n → E)).symm)
  rw [h1, Module.finrank_pi_fintype]
  simp [mul_comm]

def mkAct (Λ : Submodule (𝓞 E) (Fin n → E)) :
    stabGL Λ →* Module.End ℤ (Λ.restrictScalars ℤ : Submodule ℤ (Fin n → E)) where
  toFun g := ((Matrix.mulVecLin ((g : GL (Fin n) E) : Matrix (Fin n) (Fin n) E)).restrictScalars ℤ).restrict
    (fun x hx => (g.2 x).1 hx)
  map_one' := by
    ext x
    simp
  map_mul' a b := by
    ext x
    show ((((a * b : stabGL Λ) : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) *ᵥ (x : Fin n → E)) _ =
      (((a : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) *ᵥ
        (((b : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) *ᵥ (x : Fin n → E))) _
    rw [Matrix.mulVec_mulVec]
    rfl

theorem mkAct_apply (Λ : Submodule (𝓞 E) (Fin n → E)) (g : stabGL Λ)
    (x : (Λ.restrictScalars ℤ : Submodule ℤ (Fin n → E))) :
    ((mkAct Λ g x : (Λ.restrictScalars ℤ : Submodule ℤ (Fin n → E))) : Fin n → E) =
      ((g : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) *ᵥ (x : Fin n → E) := rfl

theorem mkAct_injective (Λ : Submodule (𝓞 E) (Fin n → E)) (hΛ : Submodule.span E (Λ : Set (Fin n → E)) = ⊤) :
    Function.Injective (mkAct Λ) := by
  intro a b hab
  apply Subtype.ext
  apply Units.ext
  have h1 : ∀ x ∈ Λ, ((a : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) *ᵥ x =
      ((b : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) *ᵥ x := by
    intro x hx
    have := congrArg (fun f => ((f ⟨x, hx⟩ : (Λ.restrictScalars ℤ : Submodule ℤ (Fin n → E))) : Fin n → E)) hab
    exact this
  have h2 : Matrix.mulVecLin ((a : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) =
      Matrix.mulVecLin ((b : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) := by
    refine LinearMap.ext_on hΛ ?_
    intro x hx
    exact h1 x hx
  exact Matrix.toLin'.injective h2

theorem mk_card_dvd (hM : Formalism.HermitianLatticeCounting.S6.MinkowskiBound) (Λ : Submodule (𝓞 E) (Fin n → E))
    (hΛ : Submodule.IsLattice E Λ) (Γ : Subgroup (GL (Fin n) E)) (hfin : Finite Γ) (hst : Γ ≤ stabGL Λ) :
    Nat.card Γ ∣ minkNum (Module.finrank ℚ E * n) := by
  have hlat := mk_isLattice Λ hΛ
  have hfree : Module.Free ℤ (Λ.restrictScalars ℤ : Submodule ℤ (Fin n → E)) := Submodule.IsLattice.free ℚ _
  have hfinm : Module.Finite ℤ (Λ.restrictScalars ℤ : Submodule ℤ (Fin n → E)) := Submodule.IsLattice.finite ℚ _
  let b := Module.finBasisOfFinrankEq ℤ (Λ.restrictScalars ℤ : Submodule ℤ (Fin n → E)) (mk_finrank Λ hΛ)
  let φ : Γ →* GL (Fin (Module.finrank ℚ E * n)) ℤ :=
    (Units.map ((LinearMap.toMatrixAlgEquiv b).toRingEquiv.toMonoidHom :
      Module.End ℤ (Λ.restrictScalars ℤ : Submodule ℤ (Fin n → E)) →* _)).comp
      (((mkAct Λ).comp (Subgroup.inclusion hst)).toHomUnits)
  have hφ : Function.Injective φ := by
    intro x y hxy
    have h1 : LinearMap.toMatrixAlgEquiv b (mkAct Λ (Subgroup.inclusion hst x)) =
        LinearMap.toMatrixAlgEquiv b (mkAct Λ (Subgroup.inclusion hst y)) := congrArg Units.val hxy
    have h2 : mkAct Λ (Subgroup.inclusion hst x) = mkAct Λ (Subgroup.inclusion hst y) :=
      (LinearMap.toMatrixAlgEquiv b).injective h1
    exact Subgroup.inclusion_injective hst (mkAct_injective Λ hΛ.span_eq_top h2)
  have hcard : Nat.card Γ = Nat.card φ.range := Nat.card_congr (MonoidHom.ofInjective hφ).toEquiv
  have hfr : Finite φ.range := Finite.of_equiv _ (MonoidHom.ofInjective hφ).toEquiv
  rw [hcard]
  exact hM _ φ.range hfr

end Lat

theorem gamMinkowski_of (hM : Formalism.HermitianLatticeCounting.S6.MinkowskiBound) : GamMinkowski := by
  intro F E _ _ _ _ _ _ hc LL _ n J L β D hU hβ c
  have hle : lev hc J β D ≤ stabGL (hatL (F := F) L) := fun x hx =>
    ((level_subgroup_finite_index F E hc LL n J L β D hβ).1 hx).2
  have hst := gamma_stabilizes_lattice F E hc n J L (lev hc J β D) hle c
  have hlat := (lattice_unimodular_at F E hc n J L (lev hc J β D) hU c).lat
  have hfin := stabilizers_finite F E hc LL n J L β D hU hβ c
  have hinj : Function.Injective ((UR hc J).subtype.comp (Gam c).subtype) :=
    Subtype.val_injective.comp Subtype.val_injective
  have hcard : Nat.card (Gam c) = Nat.card ((Gam c).map (UR hc J).subtype) :=
    Nat.card_congr ((Gam c).equivMapOfInjective _ Subtype.val_injective).toEquiv
  have hfin' : Finite ((Gam c).map (UR hc J).subtype) :=
    Finite.of_equiv _ ((Gam c).equivMapOfInjective _ Subtype.val_injective).toEquiv
  rw [hcard]
  refine mk_card_dvd hM (latAt L c) hlat _ hfin' ?_
  rintro _ ⟨γ, hγ, rfl⟩
  exact hst γ hγ

theorem gam_card_dvd (hM : Formalism.HermitianLatticeCounting.S6.MinkowskiBound)
    {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] (hc : CMData F E)
    {LL : Type} [CommRing LL] {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {L : Submodule (𝓞 E) (Fin n → E)}
    {β : GL (Fin n) (E ⊗[F] Af F)} (D : LevDat E LL n) (hU : IsDefUnimod hc J L) (hβ : IsFrame β L)
    {f N : ℕ} (hf : Module.finrank ℚ F = f) (hN : n ≤ N) (c : Cl hc J (lev hc J β D)) :
    Nat.card (Gam c) ∣ minkNum (2 * f * N) := by
  refine (gamMinkowski_of hM F E hc LL n J L β D hU hβ c).trans (minkNum_dvd ?_)
  rw [cm_finrank hc, hf]
  exact Nat.mul_le_mul_left _ hN

section LocalA

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}

def lc_eps (E : Type) [Field E] [NumberField E] [Algebra F E] (v : HeightOneSpectrum (𝓞 F)) : intAf F E :=
  ⟨Formalism.UG.P.afsplitEps E v, Formalism.UG.P.afsplit_eps_int v⟩

theorem lc_res_eps (PP : Pl E) (v : HeightOneSpectrum (𝓞 F))
    (hv : v.asIdeal = PP.asIdeal.comap (algebraMap (𝓞 F) (𝓞 E))) : resS F PP (lc_eps E v) = 1 := by
  set a : intAd F := ⟨Formalism.UG.P.afsplitI v 1, Formalism.UG.P.afsplitI_mem_intAd v 1 (one_mem _)⟩ with ha
  have e : lc_eps E v = adS F E a := by
    apply Subtype.ext
    show Formalism.UG.P.afsplitEps E v = (1 : E) ⊗ₜ[F] (Formalism.UG.P.afsplitI v 1)
    rw [Formalism.UG.P.afsplitEps, Algebra.TensorProduct.one_def, Formalism.UG.P.afsplitIE_tmul]
  have h0 : resS F PP (adS F E (1 - a)) = 0 := by
    refine resS_adS_eq_zero PP v hv _ ?_
    have : (((1 - a : intAd F)) : Af F) v = 1 - Formalism.UG.P.afsplitI v 1 v := rfl
    rw [this, Formalism.UG.P.afsplitI_self, sub_self, map_zero]; exact zero_lt_one
  rw [map_sub, map_sub, map_one, map_one, sub_eq_zero] at h0
  rw [e]; exact h0.symm

theorem resS_eq_zero_of_prV (PP : Pl E) (v : HeightOneSpectrum (𝓞 F))
    (hv : v.asIdeal = PP.asIdeal.comap (algebraMap (𝓞 F) (𝓞 E))) (s : intAf F E)
    (h : prV (E := E) v (s : E ⊗[F] Af F) = 0) : resS F PP s = 0 := by
  have h0 : lc_eps E v * s = 0 := by
    apply Subtype.ext
    show Formalism.UG.P.afsplitEps E v * (s : E ⊗[F] Af F) = 0
    rw [← Formalism.UG.P.afsplit_decomp, h, map_zero]
  have := congrArg (resS F PP) h0
  rwa [map_mul, lc_res_eps PP v hv, one_mul, map_zero] at this

theorem reduction_local : RedLocal := by
  intro F E _ _ _ _ _ n β PP v hv x hx h1
  obtain ⟨y, rfl⟩ := hx
  rw [redFn_frGL]
  have h2 : bc (prV (E := E) v) (intGL F E n y) = 1 := by
    have e : frGL β y = β * intGL F E n y * β⁻¹ := by
      simp [frGL]
    rw [e, map_mul, map_mul, map_inv] at h1
    have : bc (prV (E := E) v) (intGL F E n y) =
        (bc (prV (E := E) v) β)⁻¹ * (bc (prV (E := E) v) β * bc (prV (E := E) v) (intGL F E n y) *
          (bc (prV (E := E) v) β)⁻¹) * bc (prV (E := E) v) β := by group
    rw [this, h1]; group
  apply Units.ext
  ext i j
  show resS F PP ((y : Matrix (Fin n) (Fin n) (intAf F E)) i j) = (1 : Matrix (Fin n) (Fin n) (kP PP)) i j
  have h3 : prV (E := E) v (((y : Matrix (Fin n) (Fin n) (intAf F E)) i j : intAf F E) : E ⊗[F] Af F) =
      (1 : Matrix (Fin n) (Fin n) (E ⊗[F] v.adicCompletion F)) i j :=
    congrArg (fun g : GL (Fin n) (E ⊗[F] v.adicCompletion F) =>
      (g : Matrix (Fin n) (Fin n) (E ⊗[F] v.adicCompletion F)) i j) h2
  have h4 : resS F PP ((y : Matrix (Fin n) (Fin n) (intAf F E)) i j -
      (1 : Matrix (Fin n) (Fin n) (intAf F E)) i j) = 0 := by
    refine resS_eq_zero_of_prV PP v hv _ ?_
    rw [AddSubgroupClass.coe_sub, map_sub, h3]
    by_cases hij : i = j
    · subst hij; simp
    · simp [hij]
  rw [map_sub, sub_eq_zero] at h4
  rw [h4]
  by_cases hij : i = j
  · subst hij; simp
  · simp [hij]

end LocalA

section LocalB

theorem lc_dvd_of_sqfree {R : Type} [CommRing R] [IsDedekindDomain R] (g b : R) (hg : g ≠ 0)
    (hsq : ∀ P : Ideal R, P.IsPrime → g ∈ P → g ∉ P ^ 2)
    (hb : ∀ P : Ideal R, P.IsPrime → g ∈ P → b ∈ P) : g ∣ b := by
  classical
  by_cases hb0 : b = 0
  · rw [hb0]; exact dvd_zero g
  have hI : Ideal.span {g} ≠ (0 : Ideal R) := by
    rw [Ideal.zero_eq_bot, Ne, Ideal.span_singleton_eq_bot]; exact hg
  have hK : Ideal.span {b} ≠ (0 : Ideal R) := by
    rw [Ideal.zero_eq_bot, Ne, Ideal.span_singleton_eq_bot]; exact hb0
  have hsqf : Squarefree (Ideal.span {g} : Ideal R) := by
    rw [squarefree_iff_irreducible_sq_not_dvd_of_ne_zero hI]
    intro P hP hd
    have hPp : P.IsPrime := Ideal.isPrime_of_prime (UniqueFactorizationMonoid.irreducible_iff_prime.1 hP)
    rw [← pow_two, Ideal.dvd_span_singleton] at hd
    exact hsq P hPp (Ideal.pow_le_self two_ne_zero hd) hd
  have hnd := (UniqueFactorizationMonoid.squarefree_iff_nodup_normalizedFactors hI).1 hsqf
  have hdvd : (Ideal.span {g} : Ideal R) ∣ Ideal.span {b} := by
    rw [UniqueFactorizationMonoid.dvd_iff_normalizedFactors_le_normalizedFactors hI hK,
      Multiset.le_iff_subset hnd]
    intro P hP
    rw [Ideal.mem_normalizedFactors_iff hI] at hP
    rw [Ideal.mem_normalizedFactors_iff hK]
    refine ⟨hP.1, ?_⟩
    rw [Ideal.span_singleton_le_iff_mem]
    exact hb P hP.1 (hP.2 (Ideal.mem_span_singleton_self g))
  rw [Ideal.dvd_span_singleton, Ideal.mem_span_singleton] at hdvd
  exact hdvd

variable {E : Type} [Field E] [NumberField E] [StarRing E]

def lc_starO (E : Type) [Field E] [NumberField E] [StarRing E] : 𝓞 E ≃+* 𝓞 E :=
  RingOfIntegers.mapRingEquiv (starRingAut : E ≃+* E)

theorem lc_starO_coe (a : 𝓞 E) : ((lc_starO E a : 𝓞 E) : E) = star (a : E) := rfl

theorem lc_starO_starO (a : 𝓞 E) : lc_starO E (lc_starO E a) = a := by
  apply RingOfIntegers.ext
  rw [lc_starO_coe, lc_starO_coe, star_star]

def lc_conjPl (PP : Pl E) : Pl E where
  asIdeal := PP.asIdeal.comap (lc_starO E : 𝓞 E →+* 𝓞 E)
  isPrime := Ideal.comap_isPrime _ _
  ne_bot := by
    intro h
    obtain ⟨a, ha, ha0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot PP.ne_bot
    have h1 : lc_starO E a ∈ PP.asIdeal.comap (lc_starO E : 𝓞 E →+* 𝓞 E) := by
      rw [Ideal.mem_comap]
      show lc_starO E (lc_starO E a) ∈ PP.asIdeal
      rw [lc_starO_starO]; exact ha
    rw [h, Ideal.mem_bot] at h1
    apply ha0
    rw [← lc_starO_starO a, h1, map_zero]

theorem lc_mem_conjPl (PP : Pl E) (a : 𝓞 E) : a ∈ (lc_conjPl PP).asIdeal ↔ lc_starO E a ∈ PP.asIdeal := Iff.rfl

theorem lc_isConjPl (PP : Pl E) : IsConjPl PP (lc_conjPl PP) := by
  intro a b hab
  rw [lc_mem_conjPl]
  have : lc_starO E b = a := by
    apply RingOfIntegers.ext
    rw [lc_starO_coe, hab, star_star]
  rw [this]

theorem lc_isConjPl' (PP : Pl E) : IsConjPl (lc_conjPl PP) PP := by
  intro a b hab
  rw [lc_mem_conjPl]
  have : lc_starO E a = b := by
    apply RingOfIntegers.ext
    rw [lc_starO_coe, hab]
  rw [this]

theorem lc_mem_conjPl_sq (PP : Pl E) (a : 𝓞 E) :
    a ∈ (lc_conjPl PP).asIdeal ^ 2 ↔ lc_starO E a ∈ PP.asIdeal ^ 2 := by
  have h : (lc_conjPl PP).asIdeal = PP.asIdeal.map ((lc_starO E).symm : 𝓞 E →+* 𝓞 E) :=
    (Ideal.map_symm (lc_starO E)).symm
  have h2 : (PP.asIdeal ^ 2).map ((lc_starO E).symm : 𝓞 E →+* 𝓞 E) =
      (PP.asIdeal ^ 2).comap (lc_starO E : 𝓞 E →+* 𝓞 E) := Ideal.map_symm (lc_starO E)
  rw [h, ← Ideal.map_pow, h2]
  rfl

variable {gp : Fin 2 → ℕ} {pb : Fin 2 → 𝓞 E}

theorem lc_norm (h : IsTypeDatum gp pb) (i : Fin 2) : pb i * lc_starO E (pb i) = (gp i : 𝓞 E) := by
  apply RingOfIntegers.ext
  show ((pb i : 𝓞 E) : E) * ((lc_starO E (pb i) : 𝓞 E) : E) = (((gp i : ℕ) : 𝓞 E) : E)
  rw [lc_starO_coe, h.norm i]
  exact (map_natCast (algebraMap (𝓞 E) E) (gp i)).symm

theorem lc_gp_ne (h : IsTypeDatum gp pb) (i : Fin 2) : (gp i : 𝓞 E) ≠ 0 := by
  have := (h.prime i).ne_zero
  exact_mod_cast this

theorem lc_pb_ne (h : IsTypeDatum gp pb) (i : Fin 2) : pb i ≠ 0 := by
  intro h0
  apply lc_gp_ne h i
  rw [← lc_norm h i, h0, zero_mul]

theorem lc_cases (h : IsTypeDatum gp pb) (i : Fin 2) (PP : Pl E) (hP : (gp i : 𝓞 E) ∈ PP.asIdeal) :
    pb i ∈ PP.asIdeal ∨ pb i ∈ (lc_conjPl PP).asIdeal := by
  rw [← lc_norm h i] at hP
  exact PP.isPrime.mem_or_mem hP

theorem lc_gp_sq (h : IsTypeDatum gp pb) (i : Fin 2) (PP : Pl E) : (gp i : 𝓞 E) ∉ PP.asIdeal ^ 2 := by
  intro hsq
  have hP : (gp i : 𝓞 E) ∈ PP.asIdeal := Ideal.pow_le_self two_ne_zero hsq
  have := PP.isPrime
  rcases lc_cases h i PP hP with h1 | h1
  · rw [← lc_norm h i, mul_comm] at hsq
    rcases Ideal.IsPrime.mul_mem_pow PP.asIdeal hsq with h2 | h2
    · exact h.split i PP h1 _ (lc_starO_coe _) h2
    · exact h.unram i PP h1 h2
  · rw [← lc_norm h i] at hsq
    rcases Ideal.IsPrime.mul_mem_pow PP.asIdeal hsq with h2 | h2
    · refine h.split i (lc_conjPl PP) h1 _ (lc_starO_coe _) ?_
      rw [lc_mem_conjPl, lc_starO_starO]; exact h2
    · exact h.unram i (lc_conjPl PP) h1 ((lc_mem_conjPl_sq PP _).2 h2)

theorem lc_gp_dvd (h : IsTypeDatum gp pb) (i : Fin 2) (b : 𝓞 E)
    (hb : ∀ PP : Pl E, (gp i : 𝓞 E) ∈ PP.asIdeal → b ∈ PP.asIdeal) : (gp i : 𝓞 E) ∣ b := by
  have hbot : ∀ P : Ideal (𝓞 E), (gp i : 𝓞 E) ∈ P → P ≠ ⊥ := by
    intro P hP h0
    rw [h0, Ideal.mem_bot] at hP
    exact lc_gp_ne h i hP
  refine lc_dvd_of_sqfree _ b (lc_gp_ne h i) ?_ ?_
  · intro P hPp hP
    exact lc_gp_sq h i ⟨P, hPp, hbot P hP⟩
  · intro P hPp hP
    exact hb ⟨P, hPp, hbot P hP⟩ hP

end LocalB

section LocalC

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}

theorem lc_prV_hat (v : HeightOneSpectrum (𝓞 F)) (L : Submodule (𝓞 E) (Fin n → E)) (u : Fin n → E ⊗[F] Af F)
    (hu : u ∈ hatL (F := F) L) : (fun i => prV (E := E) v (u i)) ∈ locL v L := by
  unfold hatL latS at hu
  induction hu using Submodule.span_induction with
  | mem u hu =>
    obtain ⟨l, hl, rfl⟩ := hu
    exact Submodule.subset_span ⟨l, hl, rfl⟩
  | zero =>
    have : (fun i => prV (E := E) v ((0 : Fin n → E ⊗[F] Af F) i)) = 0 := by
      funext i; simp
    rw [this]; exact Submodule.zero_mem _
  | add a b _ _ ha hb =>
    have : (fun i => prV (E := E) v ((a + b) i)) =
        (fun i => prV (E := E) v (a i)) + (fun i => prV (E := E) v (b i)) := by
      funext i; simp
    rw [this]; exact Submodule.add_mem _ ha hb
  | smul s a _ ha =>
    have : (fun i => prV (E := E) v ((s • a) i)) =
        (⟨prV (E := E) v (s : E ⊗[F] Af F), Formalism.UG.P.afsplit_prV_int v _ s.2⟩ : intV E v) •
          (fun i => prV (E := E) v (a i)) := by
      funext i
      show prV (E := E) v ((s : E ⊗[F] Af F) * a i) = prV (E := E) v (s : E ⊗[F] Af F) * prV (E := E) v (a i)
      rw [map_mul]
    rw [this]; exact Submodule.smul_mem _ _ ha

theorem lc_IE_loc (v : HeightOneSpectrum (𝓞 F)) (L : Submodule (𝓞 E) (Fin n → E))
    (z : Fin n → E ⊗[F] v.adicCompletion F) (hz : z ∈ locL v L) :
    (fun i => Formalism.UG.P.afsplitIE v (z i)) ∈ hatL (F := F) L := by
  unfold locL latS at hz
  induction hz using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨l, hl, rfl⟩ := hz
    have : (fun i => Formalism.UG.P.afsplitIE v (inclE (F := F) (v.adicCompletion F) (l i))) =
        lc_eps E v • (fun i => inclE (F := F) (Af F) (l i)) := by
      funext i
      show _ = Formalism.UG.P.afsplitEps E v * inclE (F := F) (Af F) (l i)
      rw [← Formalism.UG.P.afsplit_decomp, Formalism.UG.P.afsplit_prV_inclE]
    rw [this]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨l, hl, rfl⟩)
  | zero =>
    have : (fun i => Formalism.UG.P.afsplitIE v ((0 : Fin n → E ⊗[F] v.adicCompletion F) i)) = 0 := by
      funext i; simp
    rw [this]; exact Submodule.zero_mem _
  | add a b _ _ ha hb =>
    have : (fun i => Formalism.UG.P.afsplitIE v ((a + b) i)) =
        (fun i => Formalism.UG.P.afsplitIE v (a i)) + (fun i => Formalism.UG.P.afsplitIE v (b i)) := by
      funext i; simp
    rw [this]; exact Submodule.add_mem _ ha hb
  | smul s a _ ha =>
    have : (fun i => Formalism.UG.P.afsplitIE v ((s • a) i)) =
        (⟨Formalism.UG.P.afsplitIE v (s : E ⊗[F] v.adicCompletion F), Formalism.UG.P.afsplit_IE_int v _ s.2⟩ : intAf F E) •
          (fun i => Formalism.UG.P.afsplitIE v (a i)) := by
      funext i
      show Formalism.UG.P.afsplitIE v ((s : E ⊗[F] v.adicCompletion F) * a i) =
        Formalism.UG.P.afsplitIE v (s : E ⊗[F] v.adicCompletion F) * Formalism.UG.P.afsplitIE v (a i)
      rw [map_mul]
    rw [this]; exact Submodule.smul_mem _ _ ha

theorem lc_map_loc (v : HeightOneSpectrum (𝓞 F)) (L : Submodule (𝓞 E) (Fin n → E))
    (X : Matrix (Fin n) (Fin n) (E ⊗[F] Af F)) (hX : ∀ u ∈ hatL (F := F) L, X *ᵥ u ∈ hatL (F := F) L)
    (w : Fin n → E ⊗[F] v.adicCompletion F) (hw : w ∈ locL v L) :
    (X.map (prV (E := E) v)) *ᵥ w ∈ locL v L := by
  unfold locL latS at hw
  induction hw using Submodule.span_induction with
  | mem w hw =>
    obtain ⟨l, hl, rfl⟩ := hw
    have h1 := lc_prV_hat v L _ (hX _ (Submodule.subset_span ⟨l, hl, rfl⟩ :
      (fun i => inclE (F := F) (Af F) (l i)) ∈ hatL (F := F) L))
    have : (fun i => prV (E := E) v ((X *ᵥ fun i => inclE (F := F) (Af F) (l i)) i)) =
        (X.map (prV (E := E) v)) *ᵥ (fun i => inclE (F := F) (v.adicCompletion F) (l i)) := by
      funext i
      rw [RingHom.map_mulVec]
      rfl
    rw [← this]; exact h1
  | zero => rw [Matrix.mulVec_zero]; exact Submodule.zero_mem _
  | add a b _ _ ha hb => rw [Matrix.mulVec_add]; exact Submodule.add_mem _ ha hb
  | smul s a _ ha => rw [Matrix.mulVec_smul]; exact Submodule.smul_mem _ _ ha

theorem lc_stab_loc (v : HeightOneSpectrum (𝓞 F)) (L : Submodule (𝓞 E) (Fin n → E))
    (x : GL (Fin n) (E ⊗[F] Af F)) (hx : x ∈ stabGL (hatL (F := F) L)) :
    bc (prV (E := E) v) x ∈ stabGL (locL v L) := by
  intro w
  constructor
  · intro hw
    exact lc_map_loc v L _ (fun u hu => (hx u).1 hu) w hw
  · intro hw
    have hx' := Subgroup.inv_mem _ hx
    have h1 := lc_map_loc v L _ (fun u hu => (hx' u).1 hu) _ hw
    have e : ((x⁻¹ : GL (Fin n) (E ⊗[F] Af F)) : Matrix (Fin n) (Fin n) (E ⊗[F] Af F)).map (prV (E := E) v) *ᵥ
        (((bc (prV (E := E) v) x : GL (Fin n) (E ⊗[F] v.adicCompletion F)) :
          Matrix (Fin n) (Fin n) (E ⊗[F] v.adicCompletion F)) *ᵥ w) = w := by
      have h2 : ((x⁻¹ : GL (Fin n) (E ⊗[F] Af F)) : Matrix (Fin n) (Fin n) (E ⊗[F] Af F)).map (prV (E := E) v) =
          ((bc (prV (E := E) v) x⁻¹ : GL (Fin n) (E ⊗[F] v.adicCompletion F)) :
            Matrix (Fin n) (Fin n) (E ⊗[F] v.adicCompletion F)) := rfl
      rw [h2, Matrix.mulVec_mulVec, ← Units.val_mul, ← map_mul, inv_mul_cancel, map_one, Units.val_one,
        Matrix.one_mulVec]
    rw [e] at h1
    exact h1

theorem lc_div (g : ℕ) (hg0 : g ≠ 0)
    (hdiv : ∀ b : 𝓞 E, (∀ PP : Pl E, (g : 𝓞 E) ∈ PP.asIdeal → b ∈ PP.asIdeal) → (g : 𝓞 E) ∣ b)
    (s : intAf F E) (hs : ∀ PP : Pl E, (g : 𝓞 E) ∈ PP.asIdeal → resS F PP s = 0) :
    ∃ t : intAf F E, s = g • t := by
  have hD : ((g : ℕ) : 𝓞 F) ≠ 0 := by exact_mod_cast hg0
  obtain ⟨b, t, ht, e⟩ := Formalism.UG.P.csGlob_approx Formalism.UG.P.integral_adele_approximation_holds ((g : ℕ) : 𝓞 F) hD
    (s : E ⊗[F] Af F) s.2
  have hC : Formalism.UG.P.levelafC E ((g : ℕ) : 𝓞 F) = ((g : ℕ) : E ⊗[F] Af F) := by
    rw [levelafC_eq_incl, map_natCast, map_natCast]
  have es : s = oToS F E b + g • (⟨t, ht⟩ : intAf F E) := by
    apply Subtype.ext
    rw [e, hC]
    show _ = inclE (F := F) (Af F) (algebraMap (𝓞 E) E b) + ((g • (⟨t, ht⟩ : intAf F E) : intAf F E) : E ⊗[F] Af F)
    rw [nsmul_eq_mul]
    simp
  have hb : ∀ PP : Pl E, (g : 𝓞 E) ∈ PP.asIdeal → b ∈ PP.asIdeal := by
    intro PP hP
    have h1 := hs PP hP
    rw [es, map_add, map_nsmul, resS_oToS, nsmul_eq_mul] at h1
    have h2 : ((g : ℕ) : kP PP) = 0 := by
      have := Ideal.Quotient.eq_zero_iff_mem.2 hP
      rwa [map_natCast] at this
    rw [h2, zero_mul, add_zero] at h1
    exact Ideal.Quotient.eq_zero_iff_mem.1 h1
  obtain ⟨b', rfl⟩ := hdiv b hb
  refine ⟨oToS F E b' + ⟨t, ht⟩, ?_⟩
  rw [es, map_mul, map_natCast, smul_add, nsmul_eq_mul, nsmul_eq_mul]

end LocalC

section LocalD

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] {n : ℕ}

omit [StarRing E] in
theorem lc_frame_mem {β : GL (Fin n) (E ⊗[F] Af F)} {L : Submodule (𝓞 E) (Fin n → E)} (hβ : IsFrame β L)
    (c : Fin n → E ⊗[F] Af F) (hc : ∀ i, c i ∈ intAf F E) :
    (β : Matrix (Fin n) (Fin n) (E ⊗[F] Af F)) *ᵥ c ∈ hatL (F := F) L := by
  refine (hβ _).2 fun i => ?_
  rw [Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec]
  exact hc i

omit [StarRing E] in
theorem lc_frGL_coe (β : GL (Fin n) (E ⊗[F] Af F)) (y : GL (Fin n) (intAf F E)) :
    ((frGL β y : GL (Fin n) (E ⊗[F] Af F)) : Matrix (Fin n) (Fin n) (E ⊗[F] Af F)) =
      (β : Matrix (Fin n) (Fin n) (E ⊗[F] Af F)) *
        (y : Matrix (Fin n) (Fin n) (intAf F E)).map (intAf F E).subtype *
        ((β⁻¹ : GL (Fin n) (E ⊗[F] Af F)) : Matrix (Fin n) (Fin n) (E ⊗[F] Af F)) := by
  show ((β * intGL F E n y * β⁻¹ : GL (Fin n) (E ⊗[F] Af F)) : Matrix (Fin n) (Fin n) (E ⊗[F] Af F)) = _
  rw [Units.val_mul, Units.val_mul]
  rfl

omit [StarRing E] in
theorem lc_one_coe (i j : Fin n) :
    (((1 : Matrix (Fin n) (Fin n) (intAf F E)) i j : intAf F E) : E ⊗[F] Af F) =
      (1 : Matrix (Fin n) (Fin n) (E ⊗[F] Af F)) i j := by
  by_cases h : i = j
  · subst h; simp
  · simp [h]

theorem lc_fwd (hc : CMData F E) (S : HSpace E) (L : Submodule (𝓞 E) (Fin S.rank → E))
    (β : GL (Fin S.rank) (E ⊗[F] Af F)) (hβ : IsFrame β L) (g : ℕ) (y : GL (Fin S.rank) (intAf F E))
    (hxl : frGL β y ∈ levelAfL hc.sig S.gram L)
    (hy : ∀ i j, ∃ t : intAf F E, (y : Matrix (Fin S.rank) (Fin S.rank) (intAf F E)) i j -
      (1 : Matrix (Fin S.rank) (Fin S.rank) (intAf F E)) i j = g • t) (v : HeightOneSpectrum (𝓞 F)) :
    InPrinc hc S v g L (bc (prV (E := E) v) (frGL β y)) := by
  have hlev : bc (prV (E := E) v) (frGL β y) ∈ levelVL hc.sig S.gram v L :=
    ⟨Formalism.UG.P.afsplit_bc_mem hc.sig S.gram v _ hxl.1, lc_stab_loc v L _ hxl.2⟩
  refine ⟨hlev, ?_⟩
  choose t ht using hy
  set M' : Matrix (Fin S.rank) (Fin S.rank) (E ⊗[F] Af F) := fun i j => ((t i j : intAf F E) : E ⊗[F] Af F) with hM'
  set N : Matrix (Fin S.rank) (Fin S.rank) (E ⊗[F] Af F) :=
    (β : Matrix (Fin S.rank) (Fin S.rank) (E ⊗[F] Af F)) * M' *
      ((β⁻¹ : GL (Fin S.rank) (E ⊗[F] Af F)) : Matrix (Fin S.rank) (Fin S.rank) (E ⊗[F] Af F)) with hN
  have hY : (y : Matrix (Fin S.rank) (Fin S.rank) (intAf F E)).map (intAf F E).subtype = 1 + g • M' := by
    ext i j
    have h1 : (y : Matrix (Fin S.rank) (Fin S.rank) (intAf F E)) i j =
        (1 : Matrix (Fin S.rank) (Fin S.rank) (intAf F E)) i j + g • t i j := by
      rw [← ht i j]; ring
    show (((y : Matrix (Fin S.rank) (Fin S.rank) (intAf F E)) i j : intAf F E) : E ⊗[F] Af F) =
      (1 : Matrix (Fin S.rank) (Fin S.rank) (E ⊗[F] Af F)) i j + g • ((t i j : intAf F E) : E ⊗[F] Af F)
    rw [h1, ← lc_one_coe]
    simp
  have hx : ((frGL β y : GL (Fin S.rank) (E ⊗[F] Af F)) : Matrix (Fin S.rank) (Fin S.rank) (E ⊗[F] Af F)) =
      1 + g • N := by
    rw [lc_frGL_coe, hY, mul_add, add_mul, mul_one, Units.mul_inv, hN, Matrix.mul_smul, Matrix.smul_mul]
  have hNL : ∀ u ∈ hatL (F := F) L, N *ᵥ u ∈ hatL (F := F) L := by
    intro u hu
    rw [hN, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
    refine lc_frame_mem hβ _ ?_
    exact Formalism.UG.P.afsplit_mulVec_mem (intAf F E) M' (fun i j => (t i j).2) _ ((hβ u).1 hu)
  intro w hw
  refine ⟨N.map (prV (E := E) v) *ᵥ w, lc_map_loc v L N hNL w hw, ?_⟩
  have hxv : ((bc (prV (E := E) v) (frGL β y) : GL (Fin S.rank) (E ⊗[F] v.adicCompletion F)) :
      Matrix (Fin S.rank) (Fin S.rank) (E ⊗[F] v.adicCompletion F)) = 1 + g • N.map (prV (E := E) v) := by
    show (prV (E := E) v).mapMatrix ((frGL β y : GL (Fin S.rank) (E ⊗[F] Af F)) :
      Matrix (Fin S.rank) (Fin S.rank) (E ⊗[F] Af F)) = 1 + g • (prV (E := E) v).mapMatrix N
    rw [hx, map_add, map_one, map_nsmul]
  rw [hxv, Matrix.add_mulVec, Matrix.one_mulVec, add_sub_cancel_left, Matrix.smul_mulVec, Nat.cast_smul_eq_nsmul]

theorem lc_bwd (hc : CMData F E) (S : HSpace E) (L : Submodule (𝓞 E) (Fin S.rank → E))
    (β : GL (Fin S.rank) (E ⊗[F] Af F)) (hβ : IsFrame β L) (g : ℕ) (PP : Pl E) (hg : (g : 𝓞 E) ∈ PP.asIdeal)
    (y : GL (Fin S.rank) (intAf F E))
    (h : InPrinc hc S (underPl F PP) g L (bc (prV (E := E) (underPl F PP)) (frGL β y))) :
    bc (resS F PP) y = 1 := by
  classical
  set v := underPl F PP with hv
  apply Units.ext
  ext k j
  set ej : Fin S.rank → E ⊗[F] Af F := Pi.single j 1 with hej
  have hejS : ∀ i, ej i ∈ intAf F E := by
    intro i
    by_cases hij : i = j
    · subst hij; rw [hej, Pi.single_eq_same]; exact one_mem _
    · rw [hej, Pi.single_eq_of_ne hij]; exact zero_mem _
  set B : Matrix (Fin S.rank) (Fin S.rank) (E ⊗[F] Af F) := (β : Matrix (Fin S.rank) (Fin S.rank) (E ⊗[F] Af F))
    with hB
  set Bi : Matrix (Fin S.rank) (Fin S.rank) (E ⊗[F] Af F) :=
    ((β⁻¹ : GL (Fin S.rank) (E ⊗[F] Af F)) : Matrix (Fin S.rank) (Fin S.rank) (E ⊗[F] Af F)) with hBi
  set Y : Matrix (Fin S.rank) (Fin S.rank) (E ⊗[F] Af F) :=
    (y : Matrix (Fin S.rank) (Fin S.rank) (intAf F E)).map (intAf F E).subtype with hY
  set X : Matrix (Fin S.rank) (Fin S.rank) (E ⊗[F] Af F) :=
    ((frGL β y : GL (Fin S.rank) (E ⊗[F] Af F)) : Matrix (Fin S.rank) (Fin S.rank) (E ⊗[F] Af F)) with hX
  have hXe : X = B * Y * Bi := lc_frGL_coe β y
  have hBiB : Bi * B = 1 := Units.inv_mul β
  set u : Fin S.rank → E ⊗[F] Af F := B *ᵥ ej with hu
  have huL : u ∈ hatL (F := F) L := lc_frame_mem hβ ej hejS
  obtain ⟨z, hz, e⟩ := h.2 _ (lc_prV_hat v L u huL)
  set z' : Fin S.rank → E ⊗[F] Af F := fun i => Formalism.UG.P.afsplitIE v (z i) with hz'
  have hz'L : z' ∈ hatL (F := F) L := lc_IE_loc v L z hz
  have hcS : ∀ i, (Bi *ᵥ z') i ∈ intAf F E := (hβ z').1 hz'L
  set d : Fin S.rank → E ⊗[F] Af F := X *ᵥ u - u - g • z' with hd
  have hd0 : (prV (E := E) v) ∘ d = 0 := by
    funext i
    show prV (E := E) v ((X *ᵥ u) i - u i - g • z' i) = 0
    rw [map_sub, map_sub, map_nsmul, RingHom.map_mulVec, hz', Formalism.UG.P.afsplit_prV_IE]
    have e' := congrFun e i
    rw [Nat.cast_smul_eq_nsmul] at e'
    have e2 : (X.map (prV (E := E) v) *ᵥ ((prV (E := E) v) ∘ u)) i - prV (E := E) v (u i) = g • z i := e'
    rw [e2, sub_self]
  have hBd : Bi *ᵥ d = Y *ᵥ ej - ej - g • (Bi *ᵥ z') := by
    rw [hd, Matrix.mulVec_sub, Matrix.mulVec_sub, Matrix.mulVec_smul, hu, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec,
      Matrix.mulVec_mulVec, hBiB, Matrix.one_mulVec, hXe]
    congr 2
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hBiB, Matrix.one_mul, Matrix.mul_assoc, hBiB, Matrix.mul_one]
  have h0 : prV (E := E) v ((Bi *ᵥ d) k) = 0 := by
    rw [RingHom.map_mulVec, hd0, Matrix.mulVec_zero]; rfl
  set s : intAf F E := (y : Matrix (Fin S.rank) (Fin S.rank) (intAf F E)) k j -
    (1 : Matrix (Fin S.rank) (Fin S.rank) (intAf F E)) k j - g • (⟨(Bi *ᵥ z') k, hcS k⟩ : intAf F E) with hs
  have hsc : ((s : intAf F E) : E ⊗[F] Af F) = (Bi *ᵥ d) k := by
    rw [hBd]
    show _ = (Y *ᵥ ej) k - ej k - g • (Bi *ᵥ z') k
    rw [hej, Matrix.mulVec_single_one]
    have h1 : (Pi.single j (1 : E ⊗[F] Af F) : Fin S.rank → E ⊗[F] Af F) k =
        (1 : Matrix (Fin S.rank) (Fin S.rank) (E ⊗[F] Af F)) k j := by
      rw [Matrix.one_apply, Pi.single_apply]
    rw [h1, ← lc_one_coe, hs]
    simp [hY]
  have hres := resS_eq_zero_of_prV PP v rfl s (by rw [hsc]; exact h0)
  have hgk : ((g : ℕ) : kP PP) = 0 := by
    have := Ideal.Quotient.eq_zero_iff_mem.2 hg
    rwa [map_natCast] at this
  rw [hs, map_sub, map_sub, map_nsmul, nsmul_eq_mul, hgk, zero_mul, sub_zero, sub_eq_zero] at hres
  show resS F PP ((y : Matrix (Fin S.rank) (Fin S.rank) (intAf F E)) k j) =
    (1 : Matrix (Fin S.rank) (Fin S.rank) (kP PP)) k j
  rw [hres]
  by_cases hkj : k = j
  · subst hkj; simp
  · simp [hkj]

theorem kgInPrinc_of (h : KgConj) : KgInPrinc := by
  intro F E _ _ _ _ _ _ hc S L β gp pb hU hβ hT x
  have hbase := base_level_eq_adelic_level F E hc S.rank S.gram L β hβ
  have hne : pb 0 * pb 1 ≠ 0 := mul_ne_zero (lc_pb_ne hT 0) (lc_pb_ne hT 1)
  constructor
  · intro hx
    have hxl : x ∈ levelAfL hc.sig S.gram L := by rw [← hbase]; exact hx.1
    have hpr : ∀ PP ∈ primesOf (pb 0 * pb 1), x ∈ princAt β PP := fun PP hP =>
      Subgroup.mem_iInf.1 (Subgroup.mem_iInf.1 hx.2 PP) hP
    refine ⟨hxl, fun i v _ => ?_⟩
    have hxU : x ∈ UA hc S.gram := hx.1.1
    obtain ⟨y, rfl⟩ := hx.1.2
    have hmem : ∀ PP : Pl E, pb i ∈ PP.asIdeal → PP ∈ primesOf (pb 0 * pb 1) := by
      intro PP hP
      refine mem_primesOf.2 ⟨hne, ?_⟩
      fin_cases i
      · exact Ideal.mul_mem_right _ _ hP
      · exact Ideal.mul_mem_left _ _ hP
    have hall : ∀ PP : Pl E, (gp i : 𝓞 E) ∈ PP.asIdeal → bc (resS F PP) y = 1 := by
      intro PP hP
      have h1 : frGL β y ∈ princAt β PP := by
        rcases lc_cases hT i PP hP with h1 | h1
        · exact hpr PP (hmem PP h1)
        · exact h F E hc S.rank S.gram L β (lc_conjPl PP) PP hU hβ (lc_isConjPl' PP) _ hxU (hpr _ (hmem _ h1))
      have h2 := (mem_princAt.1 h1).2
      rwa [redFn_frGL] at h2
    refine lc_fwd hc S L β hβ (gp i) y hxl (fun k j =>
      lc_div (gp i) (hT.prime i).ne_zero (lc_gp_dvd hT i) _ (fun PP hP => ?_)) v
    have h3 : resS F PP ((y : Matrix (Fin S.rank) (Fin S.rank) (intAf F E)) k j) =
        (1 : Matrix (Fin S.rank) (Fin S.rank) (kP PP)) k j :=
      congrArg (fun g : GL (Fin S.rank) (kP PP) => (g : Matrix (Fin S.rank) (Fin S.rank) (kP PP)) k j) (hall PP hP)
    rw [map_sub, h3]
    by_cases hkj : k = j
    · subst hkj; simp
    · simp [hkj]
  · rintro ⟨hxl, hloc⟩
    rw [← hbase] at hxl
    refine ⟨hxl, Subgroup.mem_iInf.2 fun PP => Subgroup.mem_iInf.2 fun hP => mem_princAt.2 ⟨hxl.2, ?_⟩⟩
    obtain ⟨y, rfl⟩ := hxl.2
    rw [redFn_frGL]
    obtain ⟨-, hP'⟩ := mem_primesOf.1 hP
    have key : ∀ i : Fin 2, pb i ∈ PP.asIdeal → bc (resS F PP) y = 1 := by
      intro i hi
      have hgP : (gp i : 𝓞 E) ∈ PP.asIdeal := by
        rw [← lc_norm hT i]; exact Ideal.mul_mem_right _ _ hi
      refine lc_bwd hc S L β hβ (gp i) PP hgP y (hloc i (underPl F PP) ?_)
      rw [underPl_asIdeal, Ideal.mem_comap, map_natCast]
      exact hgP
    rcases PP.isPrime.mem_or_mem hP' with h0 | h1
    · exact key 0 h0
    · exact key 1 h1

end LocalD

theorem level_in_principal_congruence : KgInPrinc := kgInPrinc_of level_conjugate

section TypeD

variable {E : Type} [Field E] [NumberField E] [StarRing E]

theorem td_absNorm_natCast (hrank : Module.finrank ℚ E = 2) (p : ℕ) :
    Ideal.absNorm (Ideal.span {(p : 𝓞 E)}) = p ^ 2 := by
  rw [Ideal.absNorm_span_singleton]
  have h : (p : 𝓞 E) = algebraMap ℤ (𝓞 E) (p : ℤ) := by simp
  rw [h, Algebra.norm_algebraMap, RingOfIntegers.rank, hrank]
  simp [Int.natAbs_pow]

theorem td_span_prime (hrank : Module.finrank ℚ E = 2) {π : 𝓞 E} {p : ℕ} (hp : p.Prime)
    (h : π * starO π = (p : 𝓞 E)) :
    (Ideal.span {π}).IsMaximal ∧ Ideal.absNorm (Ideal.span {π}) = p ∧ ¬ IsUnit π ∧ π ≠ 0 := by
  have hp0 : (p : 𝓞 E) ≠ 0 := by exact_mod_cast hp.ne_zero
  have hπ0 : π ≠ 0 := by
    rintro rfl
    rw [zero_mul] at h
    exact hp0 h.symm
  have hmul : Ideal.absNorm (Ideal.span {π}) * Ideal.absNorm (Ideal.span {starO π}) = p ^ 2 := by
    rw [← map_mul, Ideal.span_singleton_mul_span_singleton, h, td_absNorm_natCast hrank]
  have hpu : ¬ IsUnit (p : 𝓞 E) := by
    intro hu
    have h1 : Ideal.absNorm (Ideal.span {(p : 𝓞 E)}) = 1 := by
      rw [Ideal.absNorm_eq_one_iff, Ideal.span_singleton_eq_top]; exact hu
    rw [td_absNorm_natCast hrank] at h1
    have := hp.one_lt
    nlinarith
  have hnu : ¬ IsUnit π := fun h1 => hpu (h ▸ h1.mul (h1.map starOHom))
  have hu1 : Ideal.absNorm (Ideal.span {π}) ≠ 1 := by
    intro h1
    rw [Ideal.absNorm_eq_one_iff, Ideal.span_singleton_eq_top] at h1
    exact hnu h1
  have hu2 : Ideal.absNorm (Ideal.span {starO π}) ≠ 1 := by
    intro h1
    rw [Ideal.absNorm_eq_one_iff, Ideal.span_singleton_eq_top] at h1
    have h2 : IsUnit π := by
      have := h1.map starOHom
      have e : starOHom (starO π) = π := starO_starO π
      rwa [e] at this
    exact hnu h2
  have hN : Ideal.absNorm (Ideal.span {π}) = p := by
    obtain ⟨k, hk, hk'⟩ := (Nat.dvd_prime_pow hp).1 (Dvd.intro _ hmul)
    interval_cases k
    · exact absurd (by simpa using hk') hu1
    · simpa using hk'
    · exfalso
      rw [hk'] at hmul
      have hpos : 0 < p ^ 2 := by have := hp.pos; positivity
      exact hu2 (Nat.eq_of_mul_eq_mul_left hpos (by rw [hmul, mul_one]))
  have hprime : (Ideal.span {π}).IsPrime :=
    Ideal.isPrime_of_irreducible_absNorm (by rw [hN]; exact hp.prime.irreducible)
  have hbot : Ideal.span {π} ≠ ⊥ := by simpa using hπ0
  exact ⟨hprime.isMaximal hbot, hN, hnu, hπ0⟩

theorem isTypeDatum_of_quadratic (hrank : Module.finrank ℚ E = 2) {gp : Fin 2 → ℕ} {pb : Fin 2 → 𝓞 E}
    (hp : ∀ i, (gp i).Prime) (hne : gp 0 ≠ gp 1) (hnorm : ∀ i, pb i * starO (pb i) = (gp i : 𝓞 E))
    (hcop : ∀ i, IsCoprime (pb i) (starO (pb i))) : IsTypeDatum gp pb := by
  have hPP : ∀ i, ∀ PP : Pl E, pb i ∈ PP.asIdeal → PP.asIdeal = Ideal.span {pb i} := by
    intro i PP h
    have hle : Ideal.span {pb i} ≤ PP.asIdeal := by rwa [Ideal.span_singleton_le_iff_mem]
    exact ((td_span_prime hrank (hp i) (hnorm i)).1.eq_of_le PP.isPrime.ne_top hle).symm
  refine ⟨hp, hne, fun i => ?_, fun i PP h => ?_, fun i PP h h2 => ?_, fun i PP h c hc hcm => ?_⟩
  · have := congrArg (fun z : 𝓞 E => (z : E)) (hnorm i)
    simpa [starO_coe] using this
  · have h1 := (td_span_prime hrank (hp i) (hnorm i)).2.1
    rw [← hPP i PP h, Ideal.absNorm_apply, Submodule.cardQuot_apply] at h1
    exact h1
  · obtain ⟨-, -, hnu, h0⟩ := td_span_prime hrank (hp i) (hnorm i)
    rw [hPP i PP h, Ideal.span_singleton_pow, Ideal.mem_span_singleton] at h2
    obtain ⟨k, hk⟩ := h2
    apply hnu
    refine IsUnit.of_mul_eq_one k ?_
    have : pb i * (pb i * k) = pb i * 1 := by rw [mul_one]; rw [← mul_assoc, ← pow_two]; exact hk.symm
    exact mul_left_cancel₀ h0 this
  · have hc' : c = starO (pb i) := RingOfIntegers.ext hc
    obtain ⟨a, b, hab⟩ := hcop i
    apply PP.isPrime.ne_top
    rw [Ideal.eq_top_iff_one, ← hab]
    exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ h) (Ideal.mul_mem_left _ _ (hc' ▸ hcm))

end TypeD

section TypeE

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]

theorem td_gp_mem {gp : Fin 2 → ℕ} {pb : Fin 2 → 𝓞 E} (h : IsTypeDatum gp pb) (i : Fin 2) (PP : Pl E)
    (c : 𝓞 E) (hc : (c : E) = star (pb i : E)) (hm : pb i ∈ PP.asIdeal ∨ c ∈ PP.asIdeal) :
    ((gp i : ℕ) : 𝓞 E) ∈ PP.asIdeal := by
  have e : ((gp i : ℕ) : 𝓞 E) = pb i * c := by
    apply RingOfIntegers.coe_injective
    rw [map_mul]
    show algebraMap (𝓞 E) E ((gp i : ℕ) : 𝓞 E) = (pb i : E) * (c : E)
    rw [hc, h.norm i]
    simp
  rw [e]
  rcases hm with hm | hm
  · exact Ideal.mul_mem_right _ _ hm
  · exact Ideal.mul_mem_left _ _ hm

theorem isSplitSet_of_typeDatum {gp : Fin 2 → ℕ} {pb : Fin 2 → 𝓞 E} (h : IsTypeDatum gp pb) :
    IsSplitSet (primesOf (pb 0 * pb 1)) := by
  intro PP hP PP' hP' hcj
  obtain ⟨_, h1⟩ := mem_primesOf.1 hP
  obtain ⟨_, h2⟩ := mem_primesOf.1 hP'
  have hex : ∀ i, ∃ c : 𝓞 E, (c : E) = star (pb i : E) := fun i =>
    Formalism.BasicNotions.Examples₂.star_integral Formalism.BasicNotions.Examples₂.star_isIntegral (pb i)
  obtain ⟨i, hi⟩ : ∃ i, pb i ∈ PP.asIdeal := by
    rcases PP.isPrime.mem_or_mem h1 with h | h
    · exact ⟨0, h⟩
    · exact ⟨1, h⟩
  obtain ⟨i', hi'⟩ : ∃ i, pb i ∈ PP'.asIdeal := by
    rcases PP'.isPrime.mem_or_mem h2 with h | h
    · exact ⟨0, h⟩
    · exact ⟨1, h⟩
  obtain ⟨c, hc⟩ := hex i
  obtain ⟨c', hc'⟩ := hex i'
  have hcm : c ∈ PP'.asIdeal := (hcj (pb i) c hc).1 hi
  by_cases e : i' = i
  · subst e
    exact h.split i' PP' hi' c hc hcm
  · have g1 := td_gp_mem h i PP' c hc (Or.inr hcm)
    have g2 := td_gp_mem h i' PP' c' hc' (Or.inl hi')
    have hne : gp i ≠ gp i' := by
      intro hh
      have h01 := h.ne
      fin_cases i <;> fin_cases i' <;> simp_all
    have hcop : Nat.Coprime (gp i) (gp i') := (Nat.coprime_primes (h.prime i) (h.prime i')).2 hne
    obtain ⟨u, v, huv⟩ := Nat.isCoprime_iff_coprime.2 hcop
    have : (1 : 𝓞 E) ∈ PP'.asIdeal := by
      have e1 : (1 : 𝓞 E) = (u : 𝓞 E) * ((gp i : ℕ) : 𝓞 E) + (v : 𝓞 E) * ((gp i' : ℕ) : 𝓞 E) := by
        have := congrArg (fun z : ℤ => (z : 𝓞 E)) huv
        simpa using this.symm
      rw [e1]
      exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ g1) (Ideal.mul_mem_left _ _ g2)
    exact PP'.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 this)

theorem td_one_pos (hc : CMData F E) (n : ℕ) (hd : IsTotDef hc.sig (1 : Matrix (Fin n) (Fin n) E)) :
    IsTotPosDef hc.sig (1 : Matrix (Fin n) (Fin n) E) := by
  intro ι x hx
  rcases hd.2 ι with h | h
  · exact h x hx
  · exfalso
    obtain ⟨i, hi⟩ : ∃ i, x i ≠ 0 := by
      by_contra hcon
      exact hx (funext fun i => by
        by_contra h0
        exact hcon ⟨i, h0⟩)
    obtain ⟨a, ha, hneg⟩ := h (Pi.single i 1) (by
      intro h0
      have := congrFun h0 i
      simp at this)
    have h1 : hform (hc.sig : E →+* E) (1 : Matrix (Fin n) (Fin n) E) (Pi.single i 1) (Pi.single i 1) = 1 := by
      rw [← Matrix.diagonal_one, hform_diagonal, Finset.sum_eq_single i]
      · simp
      · intro j _ hj; simp [Pi.single_eq_of_ne hj]
      · intro h; exact absurd (Finset.mem_univ i) h
    rw [h1] at ha
    have : a = 1 := (algebraMap F E).injective (by rw [ha, map_one])
    rw [this, map_one] at hneg
    exact absurd hneg (by norm_num)

theorem stdIsPosUnimod (hc : CMData F E) (n : ℕ) :
    IsPosUnimod hc (stdSpace (E := E) n false).gram (stdLat (n := Fin n) (A := E) (𝓞 E)) := by
  refine ⟨standard_definite_unimodular F E hc n false, ?_⟩
  have hd := (standard_definite_unimodular F E hc n false).tdef
  have hg : ((stdSpace (E := E) n false).gram : Matrix (Fin n) (Fin n) E) = 1 := by
    rw [stdSpace_gram]; simp [Formalism.BasicNotions.Examples₂.sgn]
  have h2 : IsTotDef hc.sig (1 : Matrix (Fin n) (Fin n) E) := hg ▸ hd
  have h3 := td_one_pos hc n h2
  exact hg ▸ h3

end TypeE

section Tests

example : List.ofFn (blkOf (n := 7) 3 2) = [0, 0, 0, 1, 1, 2, 2] := by decide

example : List.ofFn (blk2 (n := 7) 3) = [0, 0, 0, 1, 1, 1, 1] := by decide

example : ∀ i j : Fin 5, symEdge 1 2 i j ↔ (i, j) ∈ [((1 : Fin 5), (2 : Fin 5)), (0, 3), (3, 4)] := by decide

example : ∀ i j : Fin 7, symEdge 2 2 i j ↔
    (i, j) ∈ [((0 : Fin 7), (1 : Fin 7)), (1, 4), (2, 3), (4, 5), (5, 6)] := by decide

example : minkNum 1 = 2 ∧ minkNum 2 = 24 ∧ minkNum 3 = 48 ∧ minkNum 4 = 5760 := by decide

def gT : GL (Fin 3) (ZMod 5) :=
  ⟨!![1, 2, 4; 0, 1, 1; 0, 0, 1], !![1, 3, 3; 0, 1, 4; 0, 0, 1], by decide, by decide⟩

example : gT ∈ unip (ZMod 5) 3 :=
  ⟨mem_blockTri.2 (by
    intro i j h
    fin_cases i <;> fin_cases j <;> first | rfl | exact absurd h (by decide)), by decide⟩

example : edgeSum supEdge gT = 3 := by decide

def gB : GL (Fin 3) (ZMod 5) :=
  ⟨!![2, 1, 1; 0, 3, 0; 0, 0, 4], !![3, 4, 3; 0, 2, 0; 0, 0, 4], by decide, by decide⟩

theorem gB_mem : gB ∈ blockTri (blkOf 1 1) :=
  mem_blockTri.2 (by
    intro i j h
    fin_cases i <;> fin_cases j <;> first | rfl | exact absurd h (by decide))

example : ((dBlk (blkOf 1 1) 1 gB : (ZMod 5)ˣ) : ZMod 5) = 3 := by rw [diag_block_det_val 1 gB_mem]; decide

example : ((dBlk (blkOf 1 1) 2 gB : (ZMod 5)ˣ) : ZMod 5) = 4 := by rw [diag_block_det_val 2 gB_mem]; decide

example : ((upperLeftBlock (show 1 ≤ 3 by decide) gB : GL (Fin 1) (ZMod 5)) : Matrix (Fin 1) (Fin 1) (ZMod 5)) = !![2] := by
  rw [upper_block_val_submatrix _ (blockTri_blkOf_le 1 1 gB_mem)]; decide

end Tests

end Formalism.L2.DIV

end
