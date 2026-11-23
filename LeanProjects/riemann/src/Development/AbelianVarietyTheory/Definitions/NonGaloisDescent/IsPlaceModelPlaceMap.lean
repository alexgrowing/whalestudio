import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnivOfNotLinearIndependent
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TranslateMemCoefLatFn
import Formalism.LocalToGlobal.ProjectiveLattices.FamilyUniformisationBasePointOrthogonalBis
import Formalism.LocalToGlobal.Columns.AdelicLemmas
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsAlgebraMapOfSigRFixed
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SupportedSubgroupSplitCommutePrimeIdempotents
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqZeroOrEqOfPlaceIdem
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IdempotentMulEqZeroOfOrthogonal
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GramMapMulInv

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum
  IsDedekindDomain NumberField Matrix
open Formalism.IndefR.Links (PolF)
open Formalism.L2.NTheta (IsIdemAt)
open scoped TensorProduct

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

namespace GlobalTheory.ExportSeries

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

section Det

variable {A : Type} [CommGroup A]

def detRoot (V : HSp D) (g : GA D V) : (AE D)ˣ := ((GlobalTheory.Member.isDetRoot_laws D V).1 g).choose

theorem isDetRoot_detRoot (V : HSp D) (g : GA D V) : IsDetRoot V g (detRoot V g) :=
  ((GlobalTheory.Member.isDetRoot_laws D V).1 g).choose_spec

def detChar (V : HSp D) (χ : (AE D)ˣ →* A) (g : GA D V) : A := χ (detRoot V g)

theorem detChar_eq {V : HSp D} {χ : (AE D)ˣ →* A} (hF : ∀ a, χ (idF D a) = 1) {g : GA D V} {z : (AE D)ˣ}
    (hz : IsDetRoot V g z) : detChar V χ g = χ z := by
  obtain ⟨a, ha⟩ := (GlobalTheory.Member.isDetRoot_laws D V).2.1 g _ _ (isDetRoot_detRoot V g) hz
  rw [ha, map_mul, hF, mul_one, detChar]

theorem detChar_mul {V : HSp D} {χ : (AE D)ˣ →* A} (hF : ∀ a, χ (idF D a) = 1) (g g' : GA D V) :
    detChar V χ (g * g') = detChar V χ g * detChar V χ g' := by
  rw [detChar_eq hF ((GlobalTheory.Member.isDetRoot_laws D V).2.2.2 _ _ _ _ (isDetRoot_detRoot V g) (isDetRoot_detRoot V g')), map_mul]
  rfl

theorem detChar_rat {V : HSp D} {χ : (AE D)ˣ →* A} (hF : ∀ a, χ (idF D a) = 1)
    (hE : ∀ x : D.host.Eˣ, χ (Units.map (incA D).toMonoidHom x) = 1) {γ : GA D V} (hγ : γ ∈ GQ V) : detChar V χ γ = 1 := by
  obtain ⟨x, hx⟩ := (GlobalTheory.Member.isDetRoot_laws D V).2.2.1 γ hγ
  rw [detChar_eq hF hx, hE]

@[simp] theorem detChar_one (V : HSp D) (g : GA D V) : detChar V (1 : (AE D)ˣ →* A) g = 1 := rfl

theorem muVal_detChar (V : HSp D) {χ : (AE D)ˣ →* Circle} (hF : ∀ a, χ (idF D a) = 1) :
    Formalism.L2.Pj.MuVal V χ fun g => ((detChar V χ g : Circle) : ℂ) :=
  ⟨(GlobalTheory.Member.isDetRoot_laws D V).1, fun _ _ hz => by beta_reduce; rw [detChar_eq hF hz]⟩

def twistBy (V : HSp D) (χ : (AE D)ˣ →* Circle) : (GA D V → ℂ) →ₗ[ℂ] (GA D V → ℂ) :=
  LinearMap.mulLeft ℂ fun g => ((detChar V χ g : Circle) : ℂ)

theorem twistBy_apply (V : HSp D) (χ : (AE D)ˣ →* Circle) (φ : GA D V → ℂ) (g : GA D V) :
    twistBy V χ φ g = ((detChar V χ g : Circle) : ℂ) * φ g := rfl

@[simp] theorem twistBy_one (V : HSp D) (φ : GA D V → ℂ) : twistBy V 1 φ = φ := by
  funext g; simp [twistBy_apply]

end Det

def idemAt (PP : Pl D.host.E) : AE D := Classical.epsilon fun e => IsIdemAt e PP

def idem (P : Finset (Pl D.host.E)) : AE D := ∑ PP ∈ P, idemAt PP

def SplitSet (P : Finset (Pl D.host.E)) : Prop := ∃ e : AE D, IsIdemSum e P

theorem idemAt_eq {e : AE D} {PP : Pl D.host.E} (h : IsIdemAt e PP) : idemAt PP = e :=
  (((GlobalTheory.IdemSupport.supported_group_and_prime_idempotents D.sp.X').2.2.1 PP e _ (Or.inl ⟨h, rfl⟩)).2.2.2.1 _ _
    (Or.inl ⟨Classical.epsilon_spec (p := fun e => IsIdemAt e PP) ⟨e, h⟩, rfl⟩)).1

theorem idem_eq {e : AE D} {P : Finset (Pl D.host.E)} (h : IsIdemSum e P) : idem P = e := by
  obtain ⟨⟨es, h1, rfl⟩, -⟩ := h
  exact Finset.sum_congr rfl fun PP hPP => idemAt_eq (h1 PP hPP)

theorem SplitSet.isIdemSum {P : Finset (Pl D.host.E)} (h : SplitSet P) : IsIdemSum (idem P) P := by
  obtain ⟨e, he⟩ := h
  rwa [idem_eq he]

theorem SplitSet.isIdemAt {P : Finset (Pl D.host.E)} (h : SplitSet P) {PP : Pl D.host.E} (hPP : PP ∈ P) :
    IsIdemAt (idemAt PP) PP := by
  obtain ⟨e, ⟨es, h1, -⟩, -⟩ := h
  rw [idemAt_eq (h1 PP hPP)]
  exact h1 PP hPP

@[simp] theorem idem_empty : idem (∅ : Finset (Pl D.host.E)) = 0 := Finset.sum_empty

theorem splitSet_empty : SplitSet (∅ : Finset (Pl D.host.E)) :=
  ⟨0, ⟨fun _ => 0, by simp, by simp⟩, zero_mul _⟩

theorem SplitSet.mul_eq_zero {P : Finset (Pl D.host.E)} (h : SplitSet P) {i j : Pl D.host.E} (hi : i ∈ P) (hj : j ∈ P)
    (hij : j ≠ i) : idemAt i * idemAt j = 0 := by
  refine (GlobalTheory.PlaceModelSum.eq_or_mul_eq_zero (h.isIdemAt hi).1 (h.isIdemAt hj).1).resolve_left fun e => hij ?_
  refine HeightOneSpectrum.ext (Ideal.ext fun x => ?_)
  by_cases hx : x = 0
  · rw [hx]; exact iff_of_true (zero_mem _) (zero_mem _)
  · rw [(h.isIdemAt hi).2 x hx, (h.isIdemAt hj).2 x hx, e]

theorem SplitSet.mul_conj {P : Finset (Pl D.host.E)} (h : SplitSet P) {i j : Pl D.host.E} (hi : i ∈ P) (hj : j ∈ P) :
    idemAt i * cA D (idemAt j) = 0 := by
  have k : ∀ l ∈ P, idemAt l * idem P = idemAt l := fun l hl =>
    GlobalTheory.PlaceModelSum.mul_sum_orth (fun a ha => (h.isIdemAt ha).1) (fun a ha b hb hab => h.mul_eq_zero ha hb hab) hl
  have h0 := h.isIdemSum.2
  rw [← k i hi, ← k j hj, RingHom.map_mul]
  linear_combination (idemAt i * cA D (idemAt j)) * h0

theorem SplitSet.mono {P P' : Finset (Pl D.host.E)} (h : SplitSet P) (hP : P' ⊆ P) : SplitSet P' := by
  refine ⟨idem P', ⟨idemAt, fun PP hPP => h.isIdemAt (hP hPP), rfl⟩, ?_⟩
  rw [idem, map_sum, Finset.sum_mul_sum]
  exact Finset.sum_eq_zero fun i hi => Finset.sum_eq_zero fun j hj => h.mul_conj (hP hi) (hP hj)

section Twist

variable {A : Type} [CommGroup A]

abbrev ResChars (D : D7) (A : Type) [CommGroup A] : Type := ∀ PP : Pl D.host.E, (kP PP)ˣ →* A

def IsResAt (χ : (AE D)ˣ →* A) (PP : Pl D.host.E) (c : (kP PP)ˣ →* A) : Prop :=
  ∀ x : (AE D)ˣ, (1 - idemAt PP) * (x : AE D) = 1 - idemAt PP →
    ∀ (hx : toEAf D (x : AE D) ∈ Formalism.L2.Herm.intAf D.host.F D.host.E) (u : (kP PP)ˣ),
      resS D.host.F PP ⟨_, hx⟩ = u → χ x = c u

def UnramOutside (χ : (AE D)ˣ →* A) (Q : Finset (Pl D.host.E)) : Prop :=
  ∀ x : (AE D)ˣ, infPart D (x : AE D) = 1 → finPart D (x : AE D) ∈ intAE D → finPart D ((x⁻¹ : (AE D)ˣ) : AE D) ∈ intAE D →
    (idem Q + cA D (idem Q)) * (x : AE D) = idem Q + cA D (idem Q) → χ x = 1

structure Twist (D : D7) (A : Type) [CommGroup A] where
  Q : Finset (Pl D.host.E)
  chi : (AE D)ˣ →* A
  res : ResChars D A

structure Twist.Good (t : Twist D A) : Prop where
  isOpen : IsOpen (t.chi.ker : Set (AE D)ˣ)
  rat : ∀ x : D.host.Eˣ, t.chi (Units.map (incA D).toMonoidHom x) = 1
  real : ∀ a, t.chi (idF D a) = 1
  split : SplitSet t.Q
  unram : UnramOutside t.chi t.Q
  res : ∀ PP ∈ t.Q, IsResAt t.chi PP (t.res PP)

def Twist.triv (A : Type) [CommGroup A] (Q : Finset (Pl D.host.E)) : Twist D A := ⟨Q, 1, fun _ => 1⟩

theorem Twist.triv_good {Q : Finset (Pl D.host.E)} (h : SplitSet Q) : (Twist.triv A Q).Good where
  isOpen := by simp [Twist.triv]
  rat _ := rfl
  real _ := rfl
  split := h
  unram _ _ _ _ _ := rfl
  res _ _ _ _ _ _ _ := rfl

theorem Twist.Good.isHeckeChar {t : Twist D Circle} (h : t.Good) : IsHeckeChar D t.chi := by
  haveI := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.isTopRing (F := D.host.F) (E := D.host.E)
  refine ⟨continuous_of_continuousAt_one t.chi ?_, h.rat⟩
  refine (continuousAt_const (y := (1 : Circle))).congr ?_
  filter_upwards [h.isOpen.mem_nhds (one_mem t.chi.ker)] with x hx using (MonoidHom.mem_ker.1 hx).symm

def Twist.resC (t : Twist D Circle) : ResChars D ℂˣ := fun PP => Circle.toUnits.comp (t.res PP)

open Classical in

def Twist.locC (t : Twist D Circle) : ResChars D ℂˣ := fun PP => if PP ∈ t.Q then t.resC PP else 1

structure UnivTwist (D : D7) (C : Type) [AddCommGroup C] where
  del : Pl D.host.E → ((AE D)ˣ →* Multiplicative C)
  kap : ResChars D (Multiplicative C)

variable {C : Type} [AddCommGroup C]

def UnivTwist.Good (u : UnivTwist D C) (Q : Finset (Pl D.host.E)) : Prop :=
  SplitSet Q ∧ ∀ PP ∈ Q, (⟨{PP}, u.del PP, u.kap⟩ : Twist D (Multiplicative C)).Good

def UnivTwist.delQ (u : UnivTwist D C) (Q : Finset (Pl D.host.E)) : (AE D)ˣ →* Multiplicative (↥Q → C) where
  toFun x := Multiplicative.ofAdd fun PP => Multiplicative.toAdd (u.del PP.1 x)
  map_one' := by ext PP; simp
  map_mul' x y := by ext PP; simp

open Classical in

def UnivTwist.spec (u : UnivTwist D C) (Q : Finset (Pl D.host.E)) (χ : Multiplicative (↥Q → C) →* A) : Twist D A where
  Q := Q
  chi := χ.comp (u.delQ Q)
  res PP := if h : PP ∈ Q then
      χ.comp ((AddMonoidHom.toMultiplicative (AddMonoidHom.single (fun _ : ↥Q => C) ⟨PP, h⟩)).comp (u.kap PP))
    else 1

theorem UnivTwist.good_empty (u : UnivTwist D C) : u.Good ∅ := ⟨splitSet_empty, fun _ h => absurd h (Finset.notMem_empty _)⟩

theorem UnivTwist.Good.mono {u : UnivTwist D C} {Q Q' : Finset (Pl D.host.E)} (h : u.Good Q) (hQ : Q' ⊆ Q) : u.Good Q' :=
  ⟨h.1.mono hQ, fun PP hPP => h.2 PP (hQ hPP)⟩

theorem UnivTwist.Good.delQ_real {u : UnivTwist D C} {Q : Finset (Pl D.host.E)} (h : u.Good Q) (a : (AF D.host.F)ˣ) :
    u.delQ Q (idF D a) = 1 := by
  ext PP
  exact congrArg Multiplicative.toAdd ((h.2 PP.1 PP.2).real a)

end Twist

structure Frame (S T : HSp D) where
  ψ : AddChar (AF D.host.F) ℂ
  θ : InfFam D
  sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ
  BS : GLR D S.rank
  BT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ
  ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)
  ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)
  βS : GL (Fin S.rank) (EAf D)
  βT : GL (Fin T.rank) (EAf D)
  f₀ : WO S T → ℂ

variable {S T : HSp D}

structure Frame.Good (F : Frame S T) : Prop where
  rank_le : T.rank ≤ S.rank
  onbS : ∀ τ, IsONBasis (gramAt D S τ) 1 (F.BS τ).val S.rank
  cartT : ∀ τ, IsCartanInv (gramAt D T τ) (F.sT τ)
  onbT : ∀ τ, IsONBasis (gramAt D T τ) (F.sT τ) (F.BT τ) (T.sig (tauE D τ)).1
  sdS : IsSelfDualC S F.ΛS
  sdT : IsSelfDualC T F.ΛT
  frS : IsFrame F.βS F.ΛS
  frT : IsFrame F.βT F.ΛT
  vac : IsVacO F.ψ F.θ S T (fun _ => 1) F.sT F.ΛS F.ΛT F.f₀

namespace Frame

variable (F : Frame S T)

abbrev lat : AddSubgroup (WO S T) := latO S T F.ΛS F.ΛT fun _ => True

def fock (f : WO S T → ℂ) : PolF D T.rank S.rank →ₗ[ℂ] (WO S T → ℂ) :=
  pureTensorO F.ψ F.θ S T (fun _ => 1) F.sT (fun τ => (F.BS τ).val) F.BT f

def placeMap (a : AE D) : (WO S T → ℂ) →ₗ[ℂ] (WO S T → ℂ) :=
  Classical.epsilon (IsPlaceModel F.ψ (symplO S T) (heisO F.ψ S T) a F.lat 1 F.f₀)

end Frame

structure TypeDat (D : D7) (r : ℕ) where
  Pg : Finset (Pl D.host.E)
  P : LevelP Pg r ℂ
  mu : ResChars D Circle

def TypeDat.muC {r : ℕ} (G : TypeDat D r) : ResChars D ℂˣ := fun PP => Circle.toUnits.comp (G.mu PP)

def TypeDat.IsFor {r : ℕ} (G : TypeDat D r) (μ : (AE D)ˣ →* Circle) : Prop := ∀ PP ∈ G.Pg, IsResAt μ PP (G.mu PP)

def TypeDat.levT {r : ℕ} (G : TypeDat D r) : LevDat D.host.E ℂ r :=
  { r := r, hr := le_rfl, t := 1, s := 0, Pg := G.Pg, Q := ∅, P := G.P, cg := fun _ _ => 1, xq := fun _ => 1 }

def TypeDat.empty (D : D7) (r : ℕ) : TypeDat D r := ⟨∅, LevelP.triv ∅ r ℂ, fun _ => 1⟩

structure PlacesOK (Pg Q : Finset (Pl D.host.E)) : Prop where
  split : ∃ P, Pg ⊆ P ∧ Q ⊆ P ∧ SplitSet P
  disj : Disjoint Pg Q
  prime : ∀ PP, PP ∈ Pg ∨ PP ∈ Q → ∀ PP', PP' = PP ∨ Lev.IsConjPl PP PP' → FractionalIdeal.count D.host.E PP' D.host.AA = 0

theorem PlacesOK.mono {Pg Q Q' : Finset (Pl D.host.E)} (h : PlacesOK Pg Q) (hQ : Q' ⊆ Q) : PlacesOK Pg Q' :=
  ⟨h.split.imp fun _ hP => ⟨hP.1, hQ.trans hP.2.1, hP.2.2⟩, h.disj.mono_right hQ,
    fun PP hPP => h.prime PP (hPP.imp_right fun h' => hQ h')⟩

theorem placesOK_empty : PlacesOK (∅ : Finset (Pl D.host.E)) ∅ :=
  ⟨⟨∅, le_rfl, le_rfl, splitSet_empty⟩, Finset.disjoint_empty_left _, fun _ h => by simp at h⟩

def halfIdem (Pg Q : Finset (Pl D.host.E)) : AE D := cA D (idem Pg) + idem Q

abbrev Reds (D : D7) (r n : ℕ) : Type := ∀ PP : Pl D.host.E, Matrix (Fin r) (Fin n) (kP PP)

namespace Frame

variable (F : Frame S T) (G : TypeDat D T.rank)

open Classical in

def datumFn (Q : Finset (Pl D.host.E)) (ω : Reds D T.rank S.rank → ℂ) : WO S T → ℂ := fun x =>
  (if IsHalf (halfIdem G.Pg Q) x ∧ IsIntM (frMapAdj S T F.βS F.βT x) then
      omegaG G.levT G.muC (fun PP => redM PP (frMapAdj S T F.βS F.βT x)) else 0) *
    (if IsHalf (halfIdem G.Pg Q) x ∧ IsIntM (frMapO S T F.βS F.βT x) then
      ω (fun PP => redM PP (frMapO S T F.βS F.βT x)) else 0)

def vec (Q : Finset (Pl D.host.E)) (ω : Reds D T.rank S.rank → ℂ) : WO S T → ℂ :=
  F.placeMap (halfIdem G.Pg Q) (F.datumFn G Q ω)

theorem datumFn_add (Q : Finset (Pl D.host.E)) (ω ω' : Reds D T.rank S.rank → ℂ) :
    F.datumFn G Q (ω + ω') = F.datumFn G Q ω + F.datumFn G Q ω' := by
  funext x
  simp only [datumFn, Pi.add_apply]
  split_ifs <;> ring

theorem datumFn_smul (Q : Finset (Pl D.host.E)) (c : ℂ) (ω : Reds D T.rank S.rank → ℂ) :
    F.datumFn G Q (c • ω) = c • F.datumFn G Q ω := by
  funext x
  simp only [datumFn, Pi.smul_apply, smul_eq_mul]
  split_ifs <;> ring

def vecL (Q : Finset (Pl D.host.E)) : (Reds D T.rank S.rank → ℂ) →ₗ[ℂ] (WO S T → ℂ) where
  toFun := F.vec G Q
  map_add' ω ω' := by rw [vec, datumFn_add, LinearMap.map_add]; rfl
  map_smul' c ω := by rw [vec, datumFn_smul, LinearMap.map_smul]; rfl

end Frame

theorem PlacesOK.isOrthSum {Pg Q : Finset (Pl D.host.E)} (h : PlacesOK Pg Q) :
    GlobalTheory.PlaceModelSum.IsOrthSum (halfIdem Pg Q) ∧ halfIdem Pg Q * cA D (halfIdem Pg Q) = 0 := by
  obtain ⟨P, h1, h2, hP⟩ := h.split
  have cc := GlobalTheory.DualPairCheck.cA_cA (D := D)
  have hne : ∀ i ∈ Pg, ∀ j ∈ Q, j ≠ i := fun i hi j hj e => Finset.disjoint_left.1 h.disj hi (e ▸ hj)
  constructor
  · refine ⟨Pl D.host.E ⊕ Pl D.host.E, Pg.disjSum Q, Sum.elim (fun i => cA D (idemAt i)) idemAt, ?_, ?_, ?_⟩
    · rintro (i | i) hi
      · exact GlobalTheory.PlaceModelSum.isSplitIdem_cA (hP.isIdemAt (h1 (by simpa using hi))).1
      · exact (hP.isIdemAt (h2 (by simpa using hi))).1
    · rintro (i | i) hi (j | j) hj hij <;> simp only [Finset.inl_mem_disjSum, Finset.inr_mem_disjSum] at hi hj <;>
        simp only [Sum.elim_inl, Sum.elim_inr]
      · rw [← RingHom.map_mul, hP.mul_eq_zero (h1 hi) (h1 hj) fun e => hij (e ▸ rfl), RingHom.map_zero]
      · rw [mul_comm]; exact hP.mul_conj (h2 hj) (h1 hi)
      · exact hP.mul_conj (h2 hi) (h1 hj)
      · exact hP.mul_eq_zero (h2 hi) (h2 hj) fun e => hij (e ▸ rfl)
    · rw [Finset.sum_disjSum, halfIdem, idem, map_sum]; rfl
  · have a1 := (hP.mono h1).isIdemSum.2
    have a2 := (hP.mono h2).isIdemSum.2
    have a3 : idem Pg * idem Q = 0 := by
      rw [idem, idem, Finset.sum_mul_sum]
      exact Finset.sum_eq_zero fun i hi => Finset.sum_eq_zero fun j hj => hP.mul_eq_zero (h1 hi) (h2 hj) (hne i hi j hj)
    have a4 : cA D (idem Pg) * cA D (idem Q) = 0 := by rw [← RingHom.map_mul, a3, RingHom.map_zero]
    rw [halfIdem, RingHom.map_add, cc]
    linear_combination a1 + a2 + a3 + a4

theorem isSBHalf_mul {m n : ℕ} {e : AE D} {Λ : AddSubgroup (Mx D m n)} {Φ Φ' : Mx D m n → ℂ} (h : IsSBHalf e Λ Φ)
    (h' : IsSBHalf e Λ Φ') : IsSBHalf e Λ fun x => Φ x * Φ' x := by
  obtain ⟨a1, k, hk, a2, a3⟩ := h
  obtain ⟨-, k', hk', b2, -⟩ := h'
  have hh : ∀ (j : ℕ) (u : Mx D m n), IsHalf e u → IsHalf e (j • u) := fun j u hu a b => by
    change e * (j • u a b) = j • u a b
    rw [mul_smul_comm, hu]
  refine ⟨fun t ht => a1 t (left_ne_zero_of_mul ht), k * k', Nat.mul_pos hk hk', fun u hu hu' t => ?_, fun t ht => ?_⟩
  · have e1 := a2 _ (nsmul_mem hu k') (hh k' u hu') t
    have e2 := b2 _ (nsmul_mem hu k) (hh k u hu') t
    rw [smul_smul] at e1 e2
    beta_reduce
    rw [e1, mul_comm k k', e2]
  · rw [mul_comm, mul_smul]
    exact nsmul_mem (a3 t (left_ne_zero_of_mul ht)) k'

namespace Frame

variable {F : Frame S T} {G : TypeDat D T.rank} {Q : Finset (Pl D.host.E)} {ω : Reds D T.rank S.rank → ℂ}

theorem isPlaceModel_placeMap (hF : F.Good) (h : PlacesOK G.Pg Q) :
    IsPlaceModel F.ψ (symplO S T) (heisO F.ψ S T) (halfIdem G.Pg Q) F.lat 1 F.f₀ (F.placeMap (halfIdem G.Pg Q)) :=
  Classical.epsilon_spec (h.isOrthSum.1.exists_model hF.vac.1 hF.sdS hF.sdT h.isOrthSum.2 hF.vac.2.lat)

theorem isSBHalf_datumFn (hF : F.Good) (h : PlacesOK G.Pg Q) (hω : ∀ y y', (∀ PP ∈ Q, y PP = y' PP) → ω y = ω y') :
    IsSBHalf (halfIdem G.Pg Q) F.lat (F.datumFn G Q ω) := by
  have hinf := h.isOrthSum.1.infPart_eq
  refine isSBHalf_mul
    (GlobalTheory.PlaceVec.isSBHalf_of_red hF.sdS.1 hF.sdT.1 hinf (frMapAdj S T F.βS F.βT) (GlobalTheory.PlaceVec.frMapAdj_add S T _ _)
      (GlobalTheory.PlaceVec.frMapAdj_up S T _ _) (GlobalTheory.PlaceVec.frMapAdj_down S T _ _) G.Pg (omegaG G.levT G.muC)
      (GlobalTheory.PlaceDatum.omegaG_congr G.levT G.muC))
    (GlobalTheory.PlaceDatum.isSBHalf_of_red _ _ (frMapO S T F.βS F.βT) (GlobalTheory.PlaceDatum.frMapO_add _ _)
      (GlobalTheory.PlaceDatum.exists_den_frMapO hF.sdS.1.fg hF.sdT.1.fg _ _) ?_ Q ω hω)
  obtain ⟨K, hK, h'⟩ := GlobalTheory.PlaceDatum.exists_nsmul_of_frMapO hF.sdS.1 hF.sdT.1 F.βS F.βT
  exact ⟨K, hK, fun t ht => h' t (GlobalTheory.PlaceDatum.infPart_of_half hinf ht)⟩

theorem isThetaAt_vec (hF : F.Good) (h : PlacesOK G.Pg Q) (hω : ∀ y y', (∀ PP ∈ Q, y PP = y' PP) → ω y = ω y') :
    IsThetaAt F.ψ (symplO S T) (heisO F.ψ S T) (halfIdem G.Pg Q) F.lat 1 F.f₀ (F.datumFn G Q ω) (F.vec G Q ω) :=
  ⟨⟨_, isPlaceModel_placeMap hF h⟩, fun _ h₂ => GlobalTheory.PlaceVec.placeModel_unique hF.vac.1 hF.sdS hF.sdT h.isOrthSum.1.idem
    h.isOrthSum.1.infPart_eq (isPlaceModel_placeMap hF h) h₂ (isSBHalf_datumFn hF h hω)⟩

end Frame

end GlobalTheory.ExportSeries

end
