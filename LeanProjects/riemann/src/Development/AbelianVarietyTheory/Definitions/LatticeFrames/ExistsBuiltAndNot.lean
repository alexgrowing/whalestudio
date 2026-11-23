import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.BuiltGIntro
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsOkPins
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.LevelNotMemRowSG

noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.L2.Th1.H GlobalTheory.ThetaMove GlobalTheory.IndefiniteRowSideFullHecke.IndexExponentDegree GlobalTheory.Mem GlobalTheory.Mem.Col2

namespace GlobalTheory.Core.AtG.BuiltModel

attribute [local instance] GlobalTheory.Mem.Col2.starE

variable {B : GlobalTheory.Mem.Base} {X : PreX B.toPre}

theorem under_inj (u : B.Word) (P Q : (B.primes X).vT u)
    (e : P.1.under (𝓞 B.host.F) = Q.1.under (𝓞 B.host.F)) : P = Q := by
  obtain ⟨hX, hPr, -⟩ := base_fields_primes_ok B X
  have hc := GlobalTheory.MuOffMove.conjP_notMem_vT hPr P.2
  have hsp := (split_of_conj_ne₂ B.fields P.1 (P.1.under (𝓞 B.host.F)) hX (fun e => hc (e.symm ▸ P.2)) rfl).2
  refine Subtype.ext (((hsp Q.1).1 (congrArg HeightOneSpectrum.asIdeal e.symm)).resolve_right fun e' => hc (e' ▸ Q.2)).symm

def errOf (I : TC B X) (l : I.Laws) (Z : TC.Later B (I.cols l)) : ErrX (I.rec7 l Z) where
  piG := X.piG
  piG_K := X.piG_K
  piG_norm := X.piG_norm
  piT := X.piT
  piT_K := X.piT_K
  piT_norm := X.piT_norm
  piT_cong u := Ideal.mem_span_singleton.2 (X.piT_cong u)
  vPl u (P : (B.primes X).vT u) := P.1.under (𝓞 B.host.F)
  vPl_inj u := under_inj u
  norm_mem_place_ideal u (P : (B.primes X).vT u) :=
    (GlobalTheory.MuOffMove.natCast_mem_under (X := B.fields) P.1 (B.T u)).2 (T_mem (base_fields_primes_ok B X).2.1 u P)

theorem builtG_errOf (I : TC B X) (h : I.Ok) (hJ : I.JetsIn) (l : I.Laws) (Z : TC.Later B (I.cols l)) :
    BuiltG (I.rec7 l Z) (errOf I l Z) :=
  builtG_intro I l Z h hJ (TrueColsTest.law0 h l) _ rfl

theorem exists_builtG : ∃ (D : D7) (EX : ErrX D), BuiltG D EX := by
  obtain ⟨B, X, I, hL, h, hJ⟩ := GlobalTheory.KerT.JetsInhab.exists_colIn_jets
  obtain ⟨Z⟩ := TrueColsTest.later (TrueColsTest.laws (I := I) h) hL
  exact ⟨_, _, builtG_errOf I h hJ _ Z⟩

theorem cong {D : D7} {EX : ErrX D} (h : BuiltG D EX) (i : Fin 2) :
    ((D.host.QS * D.host.q * D.host.d : ℕ) : 𝓞 D.host.E) ∣ EX.piG i - 1 :=
  builtG_ind (Q := fun D EX => ((D.host.QS * D.host.q * D.host.d : ℕ) : 𝓞 D.host.E) ∣ EX.piG i - 1)
    (fun _ X _ _ _ _ _ _ EX e => by rw [e]; exact X.piG_cong i) h

theorem nonempty_cls {D : D7} {EX : ErrX D} (h : BuiltG D EX) (u : D.what₂.Word) : Nonempty ((D.mem u).C.cls 0) := by
  refine builtG_ind (Q := fun D _ => ∀ u : D.what₂.Word, Nonempty ((D.mem u).C.cls 0)) ?_ h u
  intro B X I l Z _ _ _ _ _ u
  obtain ⟨b⟩ := l.idx0 I.mu0
  have : NeZero (B.R.N 0) := ⟨by have := B.R.m_add_three_le_k; unfold Ranks.N; omega⟩
  obtain ⟨p, -⟩ := exists_ptAt (R := B.R) I.sel (I.tup I.mu0) (I.cst I.mu0) (u := u) (j := 0) (DecoF.base _ _ _ _ _)
  exact ⟨(I.stp u I.mu0 0).cl b p⟩

theorem congr_piG {D : D7} {EX EX' : ErrX D} (h : BuiltG D EX) (e : EX'.piG = EX.piG) : BuiltG D EX' := by
  unfold BuiltG at h ⊢
  rwa [e]

def negG {D : D7} (EX : ErrX D) : ErrX D :=
  { EX with
    piG := fun i => -EX.piG i
    piG_K := fun i => by simpa using neg_mem (EX.piG_K i)
    piG_norm := fun i => by simpa using EX.piG_norm i }

theorem not_builtG_neg {D : D7} {EX : ErrX D} (h : BuiltG D EX) : ¬ BuiltG D (negG EX) := fun h' => by
  have h1 := cong h 0
  have h2 : ((D.host.QS * D.host.q * D.host.d : ℕ) : 𝓞 D.host.E) ∣ -EX.piG 0 - 1 := cong h' 0
  have h3 : ((D.host.QS * D.host.q * D.host.d : ℕ) : 𝓞 D.host.E) ∣ ((-2 : ℤ) : 𝓞 D.host.E) := by
    have := dvd_add h1 h2
    convert this using 1
    push_cast
    ring
  have h4 := Primes.natCast_dvd_intCast h3
  have h5 : (4 : ℤ) ∣ -2 := dvd_trans (by
    exact_mod_cast (((by decide : 4 ∣ 16).trans D.host.sixteen_dvd_QS).mul_right D.host.q).mul_right D.host.d) h4
  omega

theorem exists_built_and_not : ∃ (D : D7) (EX EX' : ErrX D), BuiltG D EX ∧ ¬ BuiltG D EX' :=
  let ⟨D, EX, h⟩ := exists_builtG
  ⟨D, EX, negG EX, h, not_builtG_neg h⟩

end GlobalTheory.Core.AtG.BuiltModel

end
