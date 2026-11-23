import Mathlib
import Formalism.LocalToGlobal.HermitianColumns.InLocalDiscriminantKernel
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.BaseDataEmbeddingConj
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsRationalUnitaryDeterminantMapRationalUnitary
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.TrueColumnChoicesHeckeCharReferenceEqOne
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.RedPEqZeroOfDiv
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.StandardRankOneLatticeOfLocal
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HostCmData
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IdeleCharacterTrivialOnLocalUnits
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HostCmEmbeddingProperties
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UnitaryDeterminantKernelOpenAndFactor
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.H90RangeEqNormOneOfIsQuad
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.OrdFNonnegOfIsInteger
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ProdAbsNormDivsDvd

noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker GlobalTheory.Mem.Chr
open ReciprocityTheory.Neutral.Bridge.HCFR Neutral.B1
open Formalism.L2.Host (HChar atFin unif ordF OverP)
open Formalism.HermitianLatticesTheory (localization₂ gmap)
open GlobalTheory.CharValCompare (IsFr)
open GlobalTheory.TopStep (IsLiftFr)
open scoped TensorProduct

namespace GlobalTheory.Mem.Col2

section Frames

variable {E : Type} [Field E] [NumberField E] [StarRing E] {n : ℕ} {ST SG Q : Finset (HeightOneSpectrum (𝓞 E))}

open Classical in

def latFr (P : HeightOneSpectrum (𝓞 E)) (N : Submodule (𝓞 E) (Sp E n)) : Sp E n ≃ₗ[E] Sp E n :=
  if localization₂ P.asIdeal N = stdAt E n P then 1 else frameAt P N

theorem isFr_latFr (P : HeightOneSpectrum (𝓞 E)) {N : Submodule (𝓞 E) (Sp E n)} (hN : Submodule.IsLattice E N) :
    IsFr P N (latFr P N) := by
  unfold latFr
  split_ifs with h
  · intro x
    rw [h]
    rfl
  · exact CharValCompare.isFr_frameAt (CharValCompare.exists_isFr P hN)

open Classical in

def ptFr (p : DecoF E n ST SG Q) (P : HeightOneSpectrum (𝓞 E)) : Sp E n ≃ₗ[E] Sp E n :=
  if h : P ∈ SG then p.deco.1.liftFr ⟨P, h⟩ else if h' : P ∈ Q then p.fr ⟨P, h'⟩ else latFr P p.deco.1.N

theorem isLiftFr_ptFr (p : DecoF E n ST SG Q) (w : SG) : IsLiftFr p.deco.1 w (ptFr p w.1) := by
  unfold ptFr
  rw [dif_pos w.2]
  exact TopStep.liftFr_spec p.deco.2 w

theorem ptFr_of_mem (p : DecoF E n ST SG Q) {P : HeightOneSpectrum (𝓞 E)} (h : P ∉ SG) (h' : P ∈ Q) :
    ptFr p P = p.fr ⟨P, h'⟩ := by
  unfold ptFr
  rw [dif_neg h, dif_pos h']

theorem isFr_ptFr (p : DecoF E n ST SG Q) (P : HeightOneSpectrum (𝓞 E)) : IsFr P p.deco.1.N (ptFr p P) := by
  by_cases h : P ∈ SG
  · exact (isLiftFr_ptFr p ⟨P, h⟩).1
  by_cases h' : P ∈ Q
  · rw [ptFr_of_mem p h h']
    exact p.2 ⟨P, h'⟩
  · unfold ptFr
    rw [dif_neg h, dif_neg h']
    exact isFr_latFr P p.deco.2.lat

theorem ptFr_congr {ST' : Finset (HeightOneSpectrum (𝓞 E))} {p : DecoF E n ST SG Q} {p' : DecoF E n ST' SG Q}
    (hN : p.deco.1.N = p'.deco.1.N) (hbe : p.deco.1.be = p'.deco.1.be) (hfr : p.fr = p'.fr) : ptFr p = ptFr p' := by
  funext P
  unfold ptFr Deco.liftFr Deco.at
  rw [hN, hbe, hfr]

theorem frsF_eq_ptFr {X : Fields} {Pr : Primes X} {R : Ranks}
    (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ} (mu : Tup X.F X.E X.K S) {u : Pr.Word} {j : ℕ}
    (p : ChPt (R := R) sel mu u j) (P : rowSG Pr sel mu) : frsF sel mu p P = ptFr p P.1 := by
  unfold frsF
  split_ifs with h
  · unfold ptFr
    rw [dif_pos h]
  · exact (ptFr_of_mem p h _).symm

def extTo (SQ : Finset (HeightOneSpectrum (𝓞 E))) (p : DecoF E n ST SG Q) : DecoF E n ST SG SQ :=
  ⟨(p.deco, fun P => ptFr p P.1), fun P => isFr_ptFr p P.1⟩

theorem extTo_deco (SQ : Finset (HeightOneSpectrum (𝓞 E))) (p : DecoF E n ST SG Q) : (extTo SQ p).deco = p.deco := rfl

theorem extTo_fr (SQ : Finset (HeightOneSpectrum (𝓞 E))) (p : DecoF E n ST SG Q) (P : SQ) :
    (extTo SQ p).fr P = ptFr p P.1 := rfl

theorem extTo_self (hd : Disjoint SG Q) (p : DecoF E n ST SG Q) : extTo Q p = p :=
  Subtype.ext (Prod.ext rfl (funext fun P => ptFr_of_mem p (Finset.disjoint_right.1 hd P.2) P.2))

open Classical in

def detIdl (SB : Finset (HeightOneSpectrum (𝓞 E))) (N : Submodule (𝓞 E) (Sp E n))
    (fr : HeightOneSpectrum (𝓞 E) → Sp E n ≃ₗ[E] Sp E n) : Ideles E :=
  (∏ P ∈ SB, localIdele E P (atFin P (LinearEquiv.det (fr P)))) *
    ∏ᶠ w : HeightOneSpectrum (𝓞 E),
      if w ∈ SB ∨ conjPrime₂ w ∈ SB then 1 else localIdele E w (atFin w (unif w)) ^ (ordSub w (detSub N)).toNat

omit [StarRing E] in

theorem finite_ordSub {N : Submodule (𝓞 E) (Sp E n)} (hN : Submodule.IsLattice E N) :
    {w | ordSub w (detSub N) ≠ 0}.Finite :=
  (ordSub_detSub_lattice E n N hN.fg hN.span_eq_top).1

open Classical in

theorem finite_detIdl (SB : Finset (HeightOneSpectrum (𝓞 E))) {N : Submodule (𝓞 E) (Sp E n)} (hN : Submodule.IsLattice E N) :
    Function.HasFiniteMulSupport fun w : HeightOneSpectrum (𝓞 E) =>
      if w ∈ SB ∨ conjPrime₂ w ∈ SB then 1 else localIdele E w (atFin w (unif w)) ^ (ordSub w (detSub N)).toNat := by
  refine (finite_ordSub hN).subset fun w hw h0 => hw ?_
  simp [h0]

open Classical in

theorem compAt_detIdl (SB : Finset (HeightOneSpectrum (𝓞 E))) {N : Submodule (𝓞 E) (Sp E n)} (hN : Submodule.IsLattice E N)
    (fr : HeightOneSpectrum (𝓞 E) → Sp E n ≃ₗ[E] Sp E n) (w : HeightOneSpectrum (𝓞 E)) :
    compAt w (detIdl SB N fr) =
      if w ∈ SB then algebraMap E _ ((LinearEquiv.det (fr w) : Eˣ) : E)
      else if conjPrime₂ w ∈ SB then 1 else algebraMap E _ ((unif w : Eˣ) : E) ^ (ordSub w (detSub N)).toNat := by
  unfold detIdl
  rw [map_mul, map_prod, MonoidHom.map_finprod _ (finite_detIdl SB hN), finprod_eq_single _ w]
  · by_cases h : w ∈ SB
    · rw [Finset.prod_eq_single_of_mem w h fun Q _ hQ => compAt_localIdele_ne hQ.symm _, compAt_localIdele_self,
        if_pos (Or.inl h), if_pos h, map_one, mul_one]
      rfl
    · rw [Finset.prod_eq_one fun Q hQ => compAt_localIdele_ne (ne_of_mem_of_not_mem hQ h).symm _, one_mul, if_neg h]
      by_cases h' : conjPrime₂ w ∈ SB
      · rw [if_pos (Or.inr h'), if_pos h', map_one]
      · rw [if_neg (not_or.2 ⟨h, h'⟩), if_neg h', map_pow, compAt_localIdele_self]
        rfl
  · intro v hv
    split_ifs
    · exact map_one _
    · rw [map_pow, compAt_localIdele_ne hv.symm, one_pow]

theorem finPartI_detIdl (SB : Finset (HeightOneSpectrum (𝓞 E))) {N : Submodule (𝓞 E) (Sp E n)} (hN : Submodule.IsLattice E N)
    (fr : HeightOneSpectrum (𝓞 E) → Sp E n ≃ₗ[E] Sp E n) : finPartI E (detIdl SB N fr) = detIdl SB N fr := by
  classical
  unfold detIdl
  rw [map_mul, map_prod, MonoidHom.map_finprod _ (finite_detIdl SB hN)]
  congr 1
  refine finprod_congr fun w => ?_
  split_ifs
  · exact map_one _
  · rw [map_pow, KerDet.finPartI_localIdele]

theorem ordSub_detSub_eq {P : HeightOneSpectrum (𝓞 E)} {N : Submodule (𝓞 E) (Sp E n)} {f : Sp E n ≃ₗ[E] Sp E n}
    (hN : Submodule.IsLattice E N) (hf : IsFr P N f) : ordSub P (detSub N) = ordF P (LinearEquiv.det f) := by
  classical
  have e : detSub N = CharValCompare.detI N := by
    unfold detSub CharValCompare.detI
    congr 1
    ext z
    constructor
    · rintro ⟨x, hx, rfl⟩
      refine ⟨(Matrix.of x).transpose, fun v hv => ?_, by rw [Matrix.det_transpose]⟩
      choose r hr using (mem_stdLat v).1 hv
      have : (Matrix.of x).transpose.mulVec v = ∑ i, r i • x i := by
        funext j
        simp [Matrix.mulVec, dotProduct, Finset.sum_apply, Algebra.smul_def, hr, mul_comm]
      rw [this]
      exact Submodule.sum_mem _ fun i _ => N.smul_mem _ (hx i)
    · rintro ⟨A, hA, rfl⟩
      refine ⟨fun i => A.mulVec (Pi.single i 1), fun i => hA _ (by simpa using single_mem_stdLat (E := E) i 1), ?_⟩
      rw [← Matrix.det_transpose]
      congr 1
      ext i j
      simp
  have hg := CharValCompare.gen_detI hf
  rw [← e] at hg
  have hl := (ordSub_detSub_lattice E n N hN.fg hN.span_eq_top).2.1 P
  have h0 : P.valuation E (CharValCompare.dt f) ≠ 0 := (Valuation.ne_zero_iff _).2 hg.1
  apply le_antisymm
  · obtain ⟨s, hs, hx⟩ := (mem_locP _ _ _).1 ((hg.2 _).2 le_rfl)
    have hs0 : s ≠ 0 := by
      rintro rfl
      exact hs (zero_mem _)
    refine hl.2 ⟨Units.mk0 _ (smul_ne_zero hs0 hg.1), hx, ?_⟩
    unfold ordF
    rw [Units.val_mk0, Algebra.smul_def, map_mul, CharValCompare.val_of_notMem hs, one_mul]
  · obtain ⟨k, hk, e'⟩ := hl.1
    rw [← e']
    unfold ordF
    exact neg_le_neg ((WithZero.log_le_log (by simp) h0).2 ((hg.2 _).1 (le_locP P _ hk)))

end Frames

section Val

variable {K Γ : Type*} [Field K] [LinearOrderedCommGroupWithZero Γ] (v : Valuation K Γ) {x y : K}

theorem val_eq_one_of_sub (h : v (x - 1) < 1) : v x = 1 := by
  have := Valuation.map_one_add_of_lt _ h
  rwa [add_sub_cancel] at this

theorem val_mul_sub_one_lt (hx : v (x - 1) < 1) (hy : v (y - 1) < 1) : v (x * y - 1) < 1 := by
  have e : x * y - 1 = x * (y - 1) + (x - 1) := by ring
  rw [e]
  refine Valuation.map_add_lt _ ?_ hx
  rwa [map_mul, val_eq_one_of_sub v hx, one_mul]

theorem val_inv_sub_one_lt (hx : v (x - 1) < 1) : v (x⁻¹ - 1) < 1 := by
  have h1 := val_eq_one_of_sub v hx
  have h0 : x ≠ 0 := by
    rintro rfl
    simp at h1
  have e : x⁻¹ - 1 = -(x⁻¹ * (x - 1)) := by field_simp; ring
  rwa [e, Valuation.map_neg, map_mul, map_inv₀, h1, inv_one, one_mul]

end Val

section Points

variable (F : Type) {E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

def adAt (P : HeightOneSpectrum (𝓞 E)) : AfE F E →+* P.adicCompletion E :=
  (Formalism.UG.evalV E P).toRingHom.comp (afIso F E).toRingHom

theorem adAt_apply (P : HeightOneSpectrum (𝓞 E)) (z : AfE F E) : adAt F P z = afIso F E z P := rfl

theorem adAt_inclE (P : HeightOneSpectrum (𝓞 E)) (x : E) :
    adAt F P (Formalism.UG.inclE (F := F) (FiniteAdeleRing (𝓞 F) F) x) = algebraMap E _ x :=
  congrArg (fun a : FiniteAdeleRing (𝓞 E) E => a P) (afIso_tmul_one F E x)

theorem adAt_finAf (P : HeightOneSpectrum (𝓞 E)) (a : Ideles E) : adAt F P (finAf F E a : AfE F E) = compAt P a :=
  congrArg (fun a : FiniteAdeleRing (𝓞 E) E => a P) (afIso_finAf F E a)

variable {F}

def HasRes (P : HeightOneSpectrum (𝓞 E)) (z : P.adicCompletion E) (c : 𝓞 E ⧸ P.asIdeal) : Prop :=
  ∃ r : 𝓞 E, Ideal.Quotient.mk P.asIdeal r = c ∧ Valued.v (z - algebraMap E _ (algebraMap (𝓞 E) E r)) < 1

theorem hasRes_coe (P : HeightOneSpectrum (𝓞 E)) (r : 𝓞 E) :
    HasRes P (algebraMap E _ (algebraMap (𝓞 E) E r)) (Ideal.Quotient.mk P.asIdeal r) :=
  ⟨r, rfl, by rw [sub_self, map_zero]; exact zero_lt_one⟩

theorem valued_algebraMap (P : HeightOneSpectrum (𝓞 E)) (x : E) :
    Valued.v (algebraMap E (P.adicCompletion E) x) = P.valuation E x :=
  HeightOneSpectrum.valuedAdicCompletion_eq_valuation' P x

theorem HasRes.unique {P : HeightOneSpectrum (𝓞 E)} {z : P.adicCompletion E} {c c' : 𝓞 E ⧸ P.asIdeal}
    (h : HasRes P z c) (h' : HasRes P z c') : c = c' := by
  obtain ⟨r, rfl, hr⟩ := h
  obtain ⟨r', rfl, hr'⟩ := h'
  have h1 := Valuation.map_sub_lt _ hr' hr
  rw [sub_sub_sub_cancel_left, ← map_sub, ← map_sub, valued_algebraMap,
    HeightOneSpectrum.valuation_lt_one_iff_mem] at h1
  exact Ideal.Quotient.eq.2 h1

def pullV {n : ℕ} (g : GL (Fin n) (AfE F E)) (x : Sp E n) : Fin n → AfE F E :=
  ((g⁻¹ : GL (Fin n) (AfE F E)) : Matrix (Fin n) (Fin n) (AfE F E)).mulVec
    fun i => Formalism.UG.inclE (F := F) (FiniteAdeleRing (𝓞 F) F) (x i)

variable [StarRing E] (hc : Formalism.BasicNotions.CMData F E) {n : ℕ} {ST SG Q : Finset (HeightOneSpectrum (𝓞 E))}

structure IsPtOf (g : GL (Fin n) (AfE F E)) (p : DecoF E n ST SG Q) : Prop where
  uni : g ∈ Formalism.L2.Herm.UstdAf hc n
  lat : Formalism.L2.Herm.Carries g (stdLat E n) p.deco.1.N
  f : ∀ (P : ST), ∀ x ∈ p.deco.1.N, ∀ i : Fin n, i.1 + 1 = n → HasRes P.1 (adAt F P.1 (pullV g x i)) (p.deco.1.f P x)
  be : ∀ (w : SG), ∀ x ∈ p.deco.1.N, ∀ i, HasRes w.1 (adAt F w.1 (pullV g x i)) (p.deco.1.be w x i)
  fr : ∀ (P : Q) (i j : Fin n), adAt F P.1 ((g : Matrix (Fin n) (Fin n) (AfE F E)) i j) =
    algebraMap E _ (p.fr P (Pi.single j 1) i)

def IsDetLift (g : GL (Fin n) (AfE F E)) (a : Ideles E) : Prop :=
  h90 hc.sig (finAf F E a) = Matrix.GeneralLinearGroup.det g

variable {hc}

theorem IsPtOf.of_extTo {SQ : Finset (HeightOneSpectrum (𝓞 E))} (hQ : Q ⊆ SQ) (hd : Disjoint SG Q)
    {g : GL (Fin n) (AfE F E)} {p : DecoF E n ST SG Q} (h : IsPtOf hc g (extTo SQ p)) : IsPtOf hc g p :=
  ⟨h.uni, h.lat, h.f, h.be, fun P i j => by
    rw [h.fr ⟨P.1, hQ P.2⟩, extTo_fr, ptFr_of_mem p (Finset.disjoint_right.1 hd P.2) P.2]⟩

theorem IsPtOf.extTo {SQ : Finset (HeightOneSpectrum (𝓞 E))} (hQ : SQ ⊆ Q) (hd : Disjoint SG SQ)
    {g : GL (Fin n) (AfE F E)} {p : DecoF E n ST SG Q} (h : IsPtOf hc g p) : IsPtOf hc g (extTo SQ p) :=
  ⟨h.uni, h.lat, h.f, h.be, fun P i j => by
    rw [h.fr ⟨P.1, hQ P.2⟩, extTo_fr, ptFr_of_mem p (Finset.disjoint_right.1 hd P.2) (hQ P.2)]⟩

variable (hc) in

theorem isPtOf_base [NeZero n] : IsPtOf hc 1 (DecoF.base E n ST SG Q) := by
  have h1 : ∀ (x : Sp E n) i, pullV (1 : GL (Fin n) (AfE F E)) x i = Formalism.UG.inclE (F := F) (FiniteAdeleRing (𝓞 F) F) (x i) :=
    fun x i => by simp [pullV]
  refine ⟨one_mem _, fun x => by simp; rfl, fun P x hx i hi => ?_, fun w x hx i => ?_, fun P i j => ?_⟩
  · replace hx : x ∈ stdLat E n := hx
    obtain ⟨r, hr⟩ := (mem_stdLat x).1 hx i
    have e : lastIdx n = i := Fin.ext (by simp [lastIdx]; omega)
    show HasRes _ _ ((Deco.base E n ST SG).f P x)
    simp only [Deco.base]
    rw [if_pos (le_locP _ _ hx), h1, adAt_inclE, e, ← hr, reduction_coe]
    exact hasRes_coe _ _
  · replace hx : x ∈ stdLat E n := hx
    obtain ⟨r, hr⟩ := (mem_stdLat x).1 hx i
    show HasRes _ _ ((Deco.base E n ST SG).be w x i)
    simp only [Deco.base]
    rw [if_pos (le_locP _ _ hx), h1, adAt_inclE, ← hr, reduction_coe]
    exact hasRes_coe _ _
  · show _ = algebraMap E _ ((Pi.single j 1 : Sp E n) i)
    rw [Units.val_one, Matrix.one_apply, Pi.single_apply]
    split_ifs <;> simp

def ratAd (F : Type) [Field F] [NumberField F] [Algebra F E] (γ : UF E n) : GL (Fin n) (AfE F E) :=
  Formalism.UG.bc (Formalism.UG.inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) (ufGL E n γ)

end Points

section Conj

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [StarRing E]

theorem conjPl_star_iff (w w' : HeightOneSpectrum (𝓞 E)) : ConjPl (starRingAut : E ≃+* E) w w' ↔ w' = conjPrime₂ w := by
  have h : ∀ w : HeightOneSpectrum (𝓞 E), ConjPl (starRingAut : E ≃+* E) w (conjPrime₂ w) := fun w => by
    rw [conjPl_iff_mem]
    intro x y hy
    have e : cO E y = x := by
      apply RingOfIntegers.ext
      show star (y : E) = x
      rw [hy]
      exact star_star _
    rw [mem_conjP, e]
  exact ⟨fun h' => (existsUnique_conjPl _ w).unique h' (h w), fun e => e ▸ h w⟩

theorem valuation_star (P : HeightOneSpectrum (𝓞 E)) (y : E) : P.valuation E (star y) = (conjPrime₂ P).valuation E y :=
  (conjPl_star_iff (conjPrime₂ P) P).2 (CharValCompare.conjP_conjP P).symm y

variable (hc : Formalism.BasicNotions.CMData F E)

theorem sigR_mem_rInt {r : AfE F E} (hr : r ∈ RInt F E) : Formalism.UG.sigR hc.sig _ r ∈ RInt F E := by
  have h : RInt F E ≤ (RInt F E).comap (Formalism.UG.sigR hc.sig _) := by
    refine Subring.closure_le.2 ?_
    rintro _ (⟨⟨_, x, rfl⟩, rfl⟩ | ⟨y, rfl⟩)
    · exact Subring.subset_closure (Or.inl ⟨⟨_, cO E x, rfl⟩, rfl⟩)
    · refine Subring.subset_closure (Or.inr ⟨y, ?_⟩)
      show _ = hc.sig 1 ⊗ₜ[F] _
      rw [map_one]
      rfl
  exact h hr

omit [StarRing E] in

theorem exists_approx_small (z : AfE F E) (T : Finset (HeightOneSpectrum (𝓞 E))) {γ : WithZero (Multiplicative ℤ)} (hγ : γ ≠ 0) :
    ∃ (y : E) (N : ℕ) (r : AfE F E), r ∈ RInt F E ∧ (∀ P ∈ T, Valued.v (N : P.adicCompletion E) < γ) ∧
      z = Formalism.UG.inclE (F := F) (FiniteAdeleRing (𝓞 F) F) y + N * r := by
  obtain ⟨N, hN, h⟩ := DetClass.exists_nat_valued_lt_finset T (fun _ => γ) fun _ => hγ
  obtain ⟨x, r, hr, e⟩ := AdeleBaseChange.exists_approx (Formalism.UG.inclE (F := F) (FiniteAdeleRing (𝓞 F) F) (N : E)⁻¹ * z)
  refine ⟨N * x, N, r, hr, h, ?_⟩
  have hN0 : (N : E) ≠ 0 := Nat.cast_ne_zero.2 hN.ne'
  have e2 := congrArg (Formalism.UG.inclE (F := F) (FiniteAdeleRing (𝓞 F) F) (N : E) * ·) e
  rw [← mul_assoc, ← map_mul, mul_inv_cancel₀ hN0, map_one, one_mul, mul_add] at e2
  rw [e2, map_mul, map_natCast]
  rfl

omit [StarRing E] in

theorem valued_nat_mul_lt {P : HeightOneSpectrum (𝓞 E)} {N : ℕ} {r : AfE F E} (hr : r ∈ RInt F E)
    {γ : WithZero (Multiplicative ℤ)} (h : Valued.v (N : P.adicCompletion E) < γ) : Valued.v (adAt F P (N * r)) < γ := by
  rw [map_mul, map_natCast, map_mul]
  exact (mul_le_of_le_one_right' ((mem_rInt_iff F E r).1 hr P)).trans_lt h

theorem sigR_inclE (y : E) : Formalism.UG.sigR hc.sig _ (Formalism.UG.inclE (F := F) (FiniteAdeleRing (𝓞 F) F) y) =
    Formalism.UG.inclE (F := F) (FiniteAdeleRing (𝓞 F) F) (star y) := rfl

theorem valued_sigR (P : HeightOneSpectrum (𝓞 E)) (z : AfE F E) :
    Valued.v (adAt F P (Formalism.UG.sigR hc.sig _ z)) = Valued.v (adAt F (conjPrime₂ P) z) := by
  classical
  have key : ∀ (P : HeightOneSpectrum (𝓞 E)) (z : AfE F E),
      Valued.v (adAt F P (Formalism.UG.sigR hc.sig _ z)) ≤ Valued.v (adAt F (conjPrime₂ P) z) := by
    intro P z
    by_contra hlt
    replace hlt := lt_of_not_ge hlt
    obtain ⟨y, N, r, hr, hN, e⟩ := exists_approx_small z {P, conjPrime₂ P} (ne_zero_of_lt hlt)
    set γ := Valued.v (adAt F P (Formalism.UG.sigR hc.sig _ z)) with hγ
    have h1 : (conjPrime₂ P).valuation E y < γ := by
      rw [← valued_algebraMap, ← adAt_inclE F, ← sub_eq_iff_eq_add.2 e, map_sub]
      exact Valuation.map_sub_lt _ hlt (valued_nat_mul_lt hr (hN _ (by simp)))
    have h2 : Valued.v (adAt F P (Formalism.UG.sigR hc.sig _ z)) < γ := by
      rw [e, map_add, map_add, sigR_inclE, adAt_inclE, map_mul, map_natCast]
      refine Valuation.map_add_lt _ ?_ (valued_nat_mul_lt (sigR_mem_rInt hc hr) (hN _ (by simp)))
      rw [valued_algebraMap, valuation_star]
      exact h1
    exact lt_irrefl _ h2
  refine le_antisymm (key P z) ?_
  have h := key (conjPrime₂ P) (Formalism.UG.sigR hc.sig _ z)
  rwa [DetClass.sigR_sigR (fun x => star_star x), CharValCompare.conjP_conjP] at h

include hc in

theorem exists_real_approx {P : HeightOneSpectrum (𝓞 E)} (hP : conjPrime₂ P ≠ P) (u : (P.adicCompletion E)ˣ) :
    ∃ k : Fˣ, Valued.v ((u : P.adicCompletion E) - algebraMap E _ (algebraMap F E k)) < Valued.v (u : P.adicCompletion E) := by
  classical
  have hγ : Valued.v (u : P.adicCompletion E) ≠ 0 := (Valuation.ne_zero_iff _).2 u.ne_zero
  obtain ⟨M, hM, hM'⟩ := DetClass.exists_nat_valued_lt (conjPrime₂ P) hγ
  have hM0 : (M : E) ≠ 0 := Nat.cast_ne_zero.2 hM.ne'
  obtain ⟨y, N, r, hr, hN, e⟩ := exists_approx_small
    (finAf F E (localIdele E P u * localIdele E (conjPrime₂ P) (atFin _ (Units.mk0 _ hM0))) : AfE F E) {P, conjPrime₂ P} hγ
  have e1 := congrArg (adAt F P) e
  rw [adAt_finAf, map_mul, compAt_localIdele_self, compAt_localIdele_ne hP.symm, mul_one, map_add, adAt_inclE] at e1
  have e2 := congrArg (adAt F (conjPrime₂ P)) e
  rw [adAt_finAf, map_mul, compAt_localIdele_self, compAt_localIdele_ne hP, one_mul, map_add, adAt_inclE] at e2
  have h1 : Valued.v ((u : P.adicCompletion E) - algebraMap E _ y) < Valued.v (u : P.adicCompletion E) := by
    rw [sub_eq_iff_eq_add'.2 e1]
    exact valued_nat_mul_lt hr (hN _ (by simp))
  have h2 : Valued.v (algebraMap E (P.adicCompletion E) (star y)) < Valued.v (u : P.adicCompletion E) := by
    rw [valued_algebraMap, valuation_star, ← valued_algebraMap, ← sub_eq_iff_eq_add.2 e2]
    refine Valuation.map_sub_lt _ ?_ (valued_nat_mul_lt hr (hN _ (by simp)))
    show Valued.v (algebraMap E ((conjPrime₂ P).adicCompletion E) (M : E)) < _
    rwa [map_natCast]
  obtain ⟨k, hk⟩ := (hc.fixed (y + star y)).1 (by rw [star_add, star_star, add_comm])
  have h3 : Valued.v ((u : P.adicCompletion E) - algebraMap E _ (algebraMap F E k)) < Valued.v (u : P.adicCompletion E) := by
    rw [hk, map_add, ← sub_sub]
    exact Valuation.map_sub_lt _ h1 h2
  refine ⟨Units.mk0 k ?_, h3⟩
  rintro rfl
  simp at h3

end Conj

section Kernel

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {R : Ranks} (H : Formalism.BasicNotions.Host R) (SG SQ : Finset (HeightOneSpectrum (𝓞 H.E)))

theorem isConjPl_iff (w w' : HeightOneSpectrum (𝓞 H.E)) : IsConjPl H w w' ↔ w' = conjPrime₂ w := by
  rw [← conjPl_star_iff, conjPl_iff_mem]
  refine forall_congr' fun x => forall_congr' fun y => ?_
  rw [← bridge_star_holds R H]
  rfl

theorem under_eq_iff (w w' : HeightOneSpectrum (𝓞 H.E)) :
    w'.under (𝓞 H.F) = w.under (𝓞 H.F) ↔ w' = w ∨ w' = conjPrime₂ w := by
  obtain ⟨c, hc, hcm, -⟩ := HostCM.host_cm R H
  rw [under_eq_iff_conjPl c hcm.rank hcm.ne, ← conjPl_star_iff]
  have e : c.toRingEquiv = (starRingAut : H.E ≃+* H.E) := RingEquiv.ext fun x => (hc x).trans (bridge_star_holds R H x).symm
  rw [e]

structure LevOk : Prop where
  cover : ∀ k v, OverP H (H.g k) v → v ∈ SG ∨ conjPrime₂ v ∈ SG
  split : ∀ P ∈ uSG SG SQ, conjPrime₂ P ∉ uSG SG SQ

theorem mem_KDq_of_local (a : Ideles H.E) (h : ∀ v : HeightOneSpectrum (𝓞 H.F), ∃ k : (H.F)ˣ, ∀ w : HeightOneSpectrum (𝓞 H.E),
    w.under (𝓞 H.F) = v → Valued.v (compAt w a / algebraMap H.E _ (algebraMap H.F H.E k)) = 1 ∧
      ((∃ i, OverP H (H.g i) w) ∨ AtQ H SQ w → Valued.v (compAt w a / algebraMap H.E _ (algebraMap H.F H.E k) - 1) < 1)) :
    a ∈ KDq H SQ := by
  classical
  choose κ hκ using h
  have hfin := (finite_level H SQ).union (IdlFact.finite_valAt_ne_one a)
  set S := hfin.toFinset.image fun w => w.under (𝓞 H.F) with hS
  set b := a / ∏ v ∈ S, locF (L := H.E) H.F v (κ v) with hb
  have hc : ∀ w, compAt w b = if w.under (𝓞 H.F) ∈ S then
      compAt w a / algebraMap H.E _ (algebraMap H.F H.E (κ (w.under (𝓞 H.F)))) else compAt w a := fun w => by
    rw [hb, map_div, map_prod, Finset.prod_congr rfl fun v _ => compAt_locF H.F w v (κ v), Finset.prod_ite_eq]
    split_ifs
    · rfl
    · exact div_one _
  have hmem : ∀ w, ((∃ i, OverP H (H.g i) w) ∨ AtQ H SQ w) ∨ IdlFact.valAt w a ≠ 1 → w.under (𝓞 H.F) ∈ S := fun w hw =>
    Finset.mem_image_of_mem _ (hfin.mem_toFinset.2 hw)
  have hl : ∀ w, (∃ i, OverP H (H.g i) w) ∨ AtQ H SQ w → Valued.v (compAt w b - 1) < 1 := fun w hw => by
    rw [hc, if_pos (hmem w (Or.inl hw))]
    exact (hκ _ w rfl).2 hw
  have hbK : b ∈ KDq H SQ := by
    refine mem_KDq_of_congQ H SQ ⟨fun w => ?_, fun i w hw => hl w (Or.inl ⟨i, hw⟩), fun w hw => hl w (Or.inr hw)⟩
    show Valued.v (compAt w b) = 1
    rw [hc]
    split_ifs with h1
    · exact (hκ _ w rfl).1
    · by_contra hne
      exact h1 (hmem w (Or.inr hne))
  rw [← div_mul_cancel a (∏ v ∈ S, locF (L := H.E) H.F v (κ v))]
  exact mul_mem hbK (prod_mem fun v _ => locF_mem_KDq H SQ v _)

variable {H SG SQ}

theorem LevOk.level (h : LevOk H SG SQ) {w : HeightOneSpectrum (𝓞 H.E)} (hw : (∃ i, OverP H (H.g i) w) ∨ AtQ H SQ w) :
    w ∈ uSG SG SQ ∨ conjPrime₂ w ∈ uSG SG SQ := by
  classical
  simp only [Finset.mem_union]
  rcases hw with ⟨i, hi⟩ | hw | ⟨v, hv, hc⟩
  · exact (h.cover i w hi).imp Or.inl Or.inl
  · exact Or.inl (Or.inr hw)
  · rw [(isConjPl_iff H v w).1 hc, CharValCompare.conjP_conjP]
    exact Or.inr (Or.inr hv)

theorem LevOk.mono (h : LevOk H SG SQ) {Q : Finset (HeightOneSpectrum (𝓞 H.E))} (hQ : Q ⊆ SQ) : LevOk H SG Q := by
  classical
  have hs : uSG SG Q ⊆ uSG SG SQ := by
    intro P
    simp only [Finset.mem_union]
    exact Or.imp_right fun h => hQ h
  exact ⟨h.cover, fun P hP h' => h.split P (hs hP) (hs h')⟩

theorem mem_KDq_of_conj (h : LevOk H SG SQ) (b : Ideles H.E)
    (h1 : ∀ w, Valued.v (compAt w b) = Valued.v (compAt (conjPrime₂ w) b))
    (h2 : ∀ P ∈ uSG SG SQ, Valued.v (compAt P b /
      adAt H.F P (Formalism.UG.sigR (host_cmData R H).sig _ (finAf H.F H.E b : AfE H.F H.E)) - 1) < 1) : b ∈ KDq H SQ := by
  refine mem_KDq_of_local H SQ b fun v => ?_
  have hb0 : ∀ w, compAt w b ≠ 0 := fun w => ((Group.isUnit b).map (compAt w)).ne_zero
  by_cases hv : ∃ P ∈ uSG SG SQ, P.under (𝓞 H.F) = v
  · obtain ⟨P, hP, rfl⟩ := hv
    have hne : conjPrime₂ (conjPrime₂ P) ≠ conjPrime₂ P := by
      rw [CharValCompare.conjP_conjP]
      exact fun e => h.split P hP (e ▸ hP)
    obtain ⟨k, hk⟩ := exists_real_approx (host_cmData R H) hne ((Group.isUnit b).map (compAt (conjPrime₂ P))).unit
    rw [IsUnit.unit_spec] at hk
    have k1 := (DetClass.div_sub_one_lt _ hk).2
    have e1 := valued_sigR (host_cmData R H) P (finAf H.F H.E b : AfE H.F H.E)
    have e2 := valued_sigR (host_cmData R H) P ((finAf H.F H.E b : AfE H.F H.E) -
      Formalism.UG.inclE (F := H.F) (FiniteAdeleRing (𝓞 H.F) H.F) (algebraMap H.F H.E k))
    rw [map_sub (Formalism.UG.sigR _ _), map_sub (adAt _ _), map_sub (adAt _ _), sigR_inclE,
      ((host_cmData R H).fixed _).2 ⟨_, rfl⟩, adAt_inclE, adAt_inclE, adAt_finAf] at e2
    rw [adAt_finAf] at e1
    rw [← e1, ← e2] at hk
    have k2 := (DetClass.div_sub_one_lt _ hk).2
    have hs0 : adAt H.F P (Formalism.UG.sigR (host_cmData R H).sig _ (finAf H.F H.E b : AfE H.F H.E)) ≠ 0 := by
      rw [← (Valued.v : Valuation (P.adicCompletion H.E) _).ne_zero_iff, e1, Valuation.ne_zero_iff]
      exact hb0 _
    have k3 : Valued.v (compAt P b / algebraMap H.E _ (algebraMap H.F H.E k) - 1) < 1 := by
      rw [← div_mul_div_cancel₀ hs0]
      exact val_mul_sub_one_lt _ (h2 P hP) k2
    refine ⟨k, fun w hw => ?_⟩
    rcases (under_eq_iff H P w).1 hw with rfl | rfl
    · exact ⟨val_eq_one_of_sub _ k3, fun _ => k3⟩
    · exact ⟨val_eq_one_of_sub _ k1, fun _ => k1⟩
  · by_cases hv' : ∃ P : HeightOneSpectrum (𝓞 H.E), P.under (𝓞 H.F) = v
    · obtain ⟨P, rfl⟩ := hv'
      obtain ⟨-, -, -, hun, -⟩ := HostCM.host_cm R H
      refine ⟨unif (P.under (𝓞 H.F)) ^ (-WithZero.log (Valued.v (compAt P b))), fun w hw => ⟨?_, fun hl => ?_⟩⟩
      · have e1 : Valued.v (compAt w b) = Valued.v (compAt P b) := by
          rcases (under_eq_iff H P w).1 hw with rfl | rfl
          · rfl
          · exact (h1 P).symm
        have e2 := hun w (unif (P.under (𝓞 H.F)))
        rw [hw, ordF_unif_self] at e2
        have e3 : w.valuation H.E (algebraMap H.F H.E (unif (P.under (𝓞 H.F)) : (H.F)ˣ)) = WithZero.exp (-1 : ℤ) := by
          rw [← e2]
          unfold ordF
          rw [neg_neg, WithZero.exp_log (by simp)]
          rfl
        rw [map_div₀, valued_algebraMap, Units.val_zpow_eq_zpow_val, map_zpow₀, map_zpow₀, e3, e1, ← WithZero.exp_zsmul]
        simp only [smul_eq_mul, mul_neg, mul_one, neg_neg]
        rw [WithZero.exp_log ((Valuation.ne_zero_iff _).2 (hb0 P)), div_self ((Valuation.ne_zero_iff _).2 (hb0 P))]
      · refine absurd ?_ hv
        rcases h.level hl with h' | h'
        · exact ⟨w, h', hw⟩
        · exact ⟨_, h', ((under_eq_iff H w _).2 (Or.inr rfl)).trans hw⟩
    · exact ⟨1, fun w hw => absurd ⟨w, hw⟩ hv'⟩

end Kernel

section Det

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {R : Ranks} (H : Formalism.BasicNotions.Host R) (SQ : Finset (HeightOneSpectrum (𝓞 H.E))) {n : ℕ}
  {ST SG Q : Finset (HeightOneSpectrum (𝓞 H.E))}

def ptIdl (p : DecoF H.E n ST SG Q) : Ideles H.E := detIdl (uSG SG SQ) p.deco.1.N (ptFr p)

def detPt (p : DecoF H.E n ST SG Q) : DtQ H SQ := QuotientGroup.mk (ptIdl H SQ p)

def xiDet (ξ : HChar H.E) (p : DecoF H.E n ST SG Q) : ℂˣ := tildeQ H SQ ξ (detPt H SQ p)

variable {H} {e : Fin R.m → R.Psi → ℚ} (C : HFrame H e)

def rhoAt (ξ : HChar H.E) (i : ℕ) (p : DecoF H.E n ST SG Q) : ℂˣ :=
  (muTilQ H SQ C.mu0 (i + 1) (detPt H SQ p))⁻¹ * (xiDet H SQ ξ p)⁻¹ *
    tildeQ H SQ C.chiPsi (detPt H SQ p) ^ (-((R.N (i + 1) / 2 : ℕ) : ℤ))

def rhoAt' (ξ : HChar H.E) (i : ℕ) (p : DecoF H.E n ST SG Q) : ℂˣ :=
  muTilQ H SQ C.mu0 (i + 1) (detPt H SQ p) * xiDet H SQ ξ p *
    tildeQ H SQ C.chiPsi (detPt H SQ p) ^ ((R.N i / 2 : ℕ) : ℤ)

@[simp] theorem xiDet_one (p : DecoF H.E n ST SG Q) : xiDet H SQ 1 p = 1 := by
  unfold xiDet
  rw [tildeQ_one]
  rfl

theorem rhoAt_one (i : ℕ) (p : DecoF H.E n ST SG Q) : rhoAt SQ C 1 i p =
    (muTilQ H SQ C.mu0 (i + 1) (detPt H SQ p))⁻¹ * tildeQ H SQ C.chiPsi (detPt H SQ p) ^ (-((R.N (i + 1) / 2 : ℕ) : ℤ)) := by
  rw [rhoAt, xiDet_one, inv_one, mul_one]

theorem rhoAt'_one (i : ℕ) (p : DecoF H.E n ST SG Q) : rhoAt' SQ C 1 i p =
    muTilQ H SQ C.mu0 (i + 1) (detPt H SQ p) * tildeQ H SQ C.chiPsi (detPt H SQ p) ^ ((R.N i / 2 : ℕ) : ℤ) := by
  rw [rhoAt', xiDet_one, mul_one]

theorem rhoAt_eq (ξ : HChar H.E) (i : ℕ) (p : DecoF H.E n ST SG Q) : rhoAt SQ C ξ i p =
    ((muTilQ H SQ C.mu0 (i + 1) * tildeQ H SQ ξ)⁻¹ * tildeQ H SQ C.chiPsi ^ (-((R.N (i + 1) / 2 : ℕ) : ℤ))) (detPt H SQ p) := by
  rw [rhoAt, xiDet, ← mul_inv]
  simp only [MonoidHom.mul_apply, MonoidHom.inv_apply, MonoidHom.zpow_apply]

theorem rhoAt'_eq (ξ : HChar H.E) (i : ℕ) (p : DecoF H.E n ST SG Q) : rhoAt' SQ C ξ i p =
    (muTilQ H SQ C.mu0 (i + 1) * tildeQ H SQ ξ * tildeQ H SQ C.chiPsi ^ ((R.N i / 2 : ℕ) : ℤ)) (detPt H SQ p) := by
  simp [rhoAt', xiDet]

theorem norm_tilde_character_eq_one (j : ℕ) (x : DtQ H SQ) : ‖((muTilQ H SQ C.mu0 j x : ℂˣ) : ℂ)‖ = 1 := by
  unfold muTilQ
  split_ifs
  · exact norm_tildeQ H SQ (C.isMu0 _).unitary x
  · simp

theorem norm_xiDet {ξ : HChar H.E} (hu : ξ.IsUnitary) (p : DecoF H.E n ST SG Q) : ‖((xiDet H SQ ξ p : ℂˣ) : ℂ)‖ = 1 :=
  norm_tildeQ H SQ hu _

theorem norm_rhoAt {ξ : HChar H.E} (hu : ξ.IsUnitary) (i : ℕ) (p : DecoF H.E n ST SG Q) :
    ‖((rhoAt SQ C ξ i p : ℂˣ) : ℂ)‖ = 1 := by
  rw [rhoAt, Units.val_mul, Units.val_mul, Units.val_inv_eq_inv_val, Units.val_inv_eq_inv_val, Units.val_zpow_eq_zpow_val,
    norm_mul, norm_mul, norm_inv, norm_inv, norm_zpow, norm_tilde_character_eq_one, norm_xiDet SQ hu, norm_tildeQ H SQ C.isChi.unitary]
  simp

theorem norm_rhoAt' {ξ : HChar H.E} (hu : ξ.IsUnitary) (i : ℕ) (p : DecoF H.E n ST SG Q) :
    ‖((rhoAt' SQ C ξ i p : ℂˣ) : ℂ)‖ = 1 := by
  rw [rhoAt', Units.val_mul, Units.val_mul, Units.val_zpow_eq_zpow_val,
    norm_mul, norm_mul, norm_zpow, norm_tilde_character_eq_one, norm_xiDet SQ hu, norm_tildeQ H SQ C.isChi.unitary]
  simp

theorem KDq_le_ker_of_tame {χ : HChar H.E} (hT : χ.TrivOn H.F) (hta : ∀ v, χ.TameAt v)
    (hu : ∀ v, ¬ ((∃ k, OverP H (H.g k) v) ∨ AtQ H SQ v) → χ.UnrAt v) : KDq H SQ ≤ (χ.1.comp (finPartI H.E)).ker := by
  refine (KDq_le_iff H SQ).2 ⟨fun a ha => ?_, fun v k => KerDet.map_finPartI_locF hT v k⟩
  refine LocTriv.eq_one_of_local H.E χ.1 χ.2.1 (finPartI H.E a) (finPartI_mem_unitIdl.2 ha.1) (fun _ => rfl) fun v x hx => ?_
  have hx' : (x : v.adicCompletion H.E) = (a : AdeleRing (𝓞 H.E) H.E).2 v := hx
  have hxu : Formalism.L2.Host.IsUnitAt v x := by
    unfold Formalism.L2.Host.IsUnitAt
    rw [hx']
    exact ha.1 v
  by_cases hv : (∃ k, OverP H (H.g k) v) ∨ AtQ H SQ v
  · refine hta v x hxu (KerDet.le_exp_neg_one ?_)
    rw [hx']
    rcases hv with ⟨k, hk⟩ | hv
    exacts [ha.2.1 k v hk, ha.2.2 v hv]
  · exact hu v hv x hxu

theorem reference_characters_factor_tame (j : Fin R.m) : KDq H SQ ≤ ((C.mu0 j).1.comp (finPartI H.E)).ker :=
  KDq_le_ker_of_tame SQ (C.isMu0 j).triv (C.isMu0 j).tame fun v hv => (C.isMu0 j).unr v fun k hk => hv (Or.inl ⟨k, hk⟩)

theorem chiPsi_factors : KDq H SQ ≤ (C.chiPsi.1.comp (finPartI H.E)).ker :=
  KDq_le_ker_of_tame SQ C.isChi.triv (fun v x hx _ => C.isChi.unr v x hx) fun v _ => C.isChi.unr v

theorem xiDet_eq {ξ : HChar H.E} (h : KDq H SQ ≤ (ξ.1.comp (finPartI H.E)).ker) (p : DecoF H.E n ST SG Q) :
    xiDet H SQ ξ p = ξ.1 (ptIdl H SQ p) := by
  rw [xiDet, detPt, tildeQ_mk H SQ h, ptIdl, finPartI_detIdl _ p.deco.2.lat]

theorem rhoAt_eq_hecke {ξ : HChar H.E} (h : KDq H SQ ≤ (ξ.1.comp (finPartI H.E)).ker) (j : Fin R.m) (p : DecoF H.E n ST SG Q) :
    rhoAt SQ C ξ j.1 p = ((C.mu0 j * ξ).1 (ptIdl H SQ p))⁻¹ * C.chiPsi.1 (ptIdl H SQ p) ^ (-((R.N (j.1 + 1) / 2 : ℕ) : ℤ)) := by
  rw [rhoAt, muTilQ_succ, xiDet_eq SQ h, ← xiDet_eq SQ (chiPsi_factors SQ C), ← mul_inv, ← xiDet,
    xiDet_eq SQ (reference_characters_factor_tame SQ C j)]
  rfl

theorem rhoAt'_eq_hecke {ξ : HChar H.E} (h : KDq H SQ ≤ (ξ.1.comp (finPartI H.E)).ker) (j : Fin R.m) (p : DecoF H.E n ST SG Q) :
    rhoAt' SQ C ξ j.1 p = (C.mu0 j * ξ).1 (ptIdl H SQ p) * C.chiPsi.1 (ptIdl H SQ p) ^ ((R.N j.1 / 2 : ℕ) : ℤ) := by
  rw [rhoAt', muTilQ_succ, xiDet_eq SQ h, ← xiDet_eq SQ (chiPsi_factors SQ C), ← xiDet,
    xiDet_eq SQ (reference_characters_factor_tame SQ C j)]
  rfl

variable (H) in

def toDtQ {SQ : Finset (HeightOneSpectrum (𝓞 H.E))} (h : Q ⊆ SQ) : DtQ H SQ →* DtQ H Q :=
  QuotientGroup.map (KDq H SQ) (KDq H Q) (MonoidHom.id _) (KDq_anti H h)

theorem toDtQ_mk {SQ : Finset (HeightOneSpectrum (𝓞 H.E))} (h : Q ⊆ SQ) (a : Ideles H.E) :
    toDtQ H h (QuotientGroup.mk a) = QuotientGroup.mk a := rfl

theorem tildeQ_toDtQ {SQ : Finset (HeightOneSpectrum (𝓞 H.E))} (h : Q ⊆ SQ) {χ : HChar H.E}
    (hχ : KDq H Q ≤ (χ.1.comp (finPartI H.E)).ker) (x : DtQ H SQ) : tildeQ H Q χ (toDtQ H h x) = tildeQ H SQ χ x := by
  obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective x
  rw [toDtQ_mk, tildeQ_mk H Q hχ, tildeQ_mk H SQ ((KDq_anti H h).trans hχ)]

end Det

section OverBase

theorem levOk_base (B : Base) (X : PreX B.toPre) : LevOk B.host (B.primes X).vGs ∅ := by
  classical
  letI := B.host.cmStar
  have hPr := (BasePrimes.primes_ok B X).1
  have h0 : ∀ i, B.fields.conjO ((B.primes X).piG i) ≠ 0 := fun i h => by
    have := hPr.piG_norm i
    rw [h, mul_zero] at this
    exact (hPr.g_prime i).ne_zero (Nat.cast_eq_zero.1 this.symm)
  have hm : ∀ w, w ∈ (B.primes X).vGs ↔ ∃ i, B.fields.conjO ((B.primes X).piG i) ∈ w.asIdeal := fun w => by
    unfold Primes.vGs Primes.vG
    simp only [Finset.mem_union, mem_divs (h0 _), Fin.exists_fin_two]
  refine ⟨fun k v hv => ?_, fun P hP hP' => ?_⟩
  · have h1 : (B.primes X).piG k * B.fields.conjO ((B.primes X).piG k) ∈ v.asIdeal := by
      rw [hPr.piG_norm]
      exact hv
    rcases v.isPrime.mem_or_mem h1 with h | h
    · refine Or.inr ((hm _).2 ⟨k, ?_⟩)
      show B.fields.conjO (B.fields.conjO _) ∈ v.asIdeal
      rwa [BasePrimes.conjO_conjO]
    · exact Or.inl ((hm _).2 ⟨k, h⟩)
  · simp only [Finset.mem_union, Finset.notMem_empty, or_false] at hP hP'
    obtain ⟨i, hi⟩ := (hm _).1 hP
    obtain ⟨j, hj⟩ := (hm _).1 hP'
    replace hj : B.fields.conjO (B.fields.conjO ((B.primes X).piG j)) ∈ P.asIdeal := hj
    rw [BasePrimes.conjO_conjO] at hj
    apply one_notMem P
    by_cases hij : i = j
    · subst hij
      obtain ⟨a, b, e⟩ := hPr.piG_cop i
      rw [← e]
      exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ hj) (Ideal.mul_mem_left _ _ hi)
    · have h1 : ((B.primes X).g i : 𝓞 B.fields.E) ∈ P.asIdeal := by
        rw [← hPr.piG_norm i]; exact Ideal.mul_mem_left _ _ hi
      have h2 : ((B.primes X).g j : 𝓞 B.fields.E) ∈ P.asIdeal := by
        rw [← hPr.piG_norm j]; exact Ideal.mul_mem_right _ _ hj
      have hne : (B.primes X).g i ≠ (B.primes X).g j := by
        have h01 := hPr.g_ne
        fin_cases i <;> fin_cases j
        exacts [absurd rfl hij, h01, h01.symm, absurd rfl hij]
      obtain ⟨a, b, e⟩ := (Nat.isCoprime_iff_coprime.2 ((Nat.coprime_primes (hPr.g_prime i) (hPr.g_prime j)).2 hne)).map
        (Int.castRingHom (𝓞 B.fields.E))
      rw [← e]
      exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ (by simpa using h1)) (Ideal.mul_mem_left _ _ (by simpa using h2))

example (B : Base) (X : PreX B.toPre) (I : ColIn B X) (a : I.ι) (u : B.Word) (i : ℕ)
    (p : ChPt (Pr := B.primes X) (R := B.R) I.sel (I.tup a) u i) : ℂˣ := rhoAt I.SQ I.C (I.xi a) i p

example {E : Type} [Field E] [NumberField E] [StarRing E] (P : HeightOneSpectrum (𝓞 E)) (f : Sp E 1 ≃ₗ[E] Sp E 1) :
    compAt P (detIdl {P} (stdLat E 1) fun _ => f) = algebraMap E _ ((LinearEquiv.det f : Eˣ) : E) := by
  rw [compAt_detIdl _ stdLat_lattice, if_pos (Finset.mem_singleton_self P)]

end OverBase

end GlobalTheory.Mem.Col2
