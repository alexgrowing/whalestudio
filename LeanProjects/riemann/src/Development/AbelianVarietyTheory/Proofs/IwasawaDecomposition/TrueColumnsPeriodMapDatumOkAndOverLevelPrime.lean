import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LatAtLattice
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PrimeNotMemOfMemQE
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BaseFieldsPrimesOk

noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.Col2.PerLaw

variable {B : Base} {X : PreX B.toPre} {I : TC B X}

theorem piT_notMem_Q (h : I.Ok) (u : B.Word) (a : I.ι) (P : I.Q a) : (B.primes X).piT u ∉ P.1.asIdeal := fun hm => by
  have hPr := (base_fields_primes_ok B X).2.1
  refine T_notMem_QE I.sel (I.tup a) u hPr h.sel_ok (h.T_mem u) P.1 P.2 ?_
  rw [← hPr.piT_norm u]
  exact P.1.asIdeal.mul_mem_right _ hm

theorem til_deco (h : I.Ok) (u : B.Word) (a : I.ι) (b : (I.perIn u a).S'.β) (p : (I.stX a).D b) :
    ((I.perIn u a).til b p).1.1.deco = DecoSet.tilH (N_m_succ B.R) ((B.primes X).piT u) p.1.1.deco :=
  tilF_deco I.sel (I.tup a) (base_fields_primes_ok B X).2.1 u (piT_notMem_Q h u a) p.1.1

theorem pref_m (u : B.Word) (a : I.ι) (b : (I.stp0 u a B.R.m).β) (q : (I.stp0 u a B.R.m).D b) :
    I.pref u a B.R.m b q ↔ ∃ d, q.1.1 = tilF (Pr := B.primes X) (R := B.R) I.sel (I.tup a) u d := by
  have hm := B.R.two_le_m
  rw [← topLev_pref_m I.Ch I.sel (I.tup a) (I.cst a) I.Ps u]
  exact ⟨fun h => h.2.2, fun h => ⟨fun e => by omega, fun e => by omega, h⟩⟩

theorem stX_ok (a : I.ι) : (I.stX a).Ok :=
  stepY_ok (Ys.triv B.fields _) Unit (fun _ => rowTyG I.Ch I.Ps) (fun _ => levQX B.R I.sel (I.tup a)) (fun _ => True)
    (base_fields_primes_ok B X).1 (fun _ => levQX_finiteIndex I.sel (I.tup a))
    (fun _ P g => (levQX_root (R := B.R) I.sel (I.tup a) P).imp fun _ hm => ⟨hm.1, hm.2 g⟩) fun _ _ => Set.finite_singleton _

set_option maxHeartbeats 1600000 in

theorem perIn_ok (h : I.Ok) (u : B.Word) (a : I.ι) : (I.perIn u a).Ok where
  step := stX_ok a
  til_smul _ g p := Subtype.ext (Prod.ext
    (tilF_extTop I.Ch I.sel (I.tup a) (I.cst a) I.Ps (base_fields_primes_ok B X).2.1 u (piT_notMem_Q h u a) g p.1.1)
    (Set.image_empty _).symm)
  ext_inj _ := extTop_injective I.Ch I.sel (I.tup a) (I.cst a) I.Ps
  gam_ini _ g x := (congrArg (iniH (N_m_succ B.R)) (toGLm_mulVec (extUH (N_m_succ B.R) g.1).1 x)).trans
    ((iniH_extUH _ g.1 x).trans (toGLm_mulVec g.1.1 _).symm)
  gam_last _ g x := (congrFun (toGLm_mulVec (extUH (N_m_succ B.R) g.1).1 x) _).trans (extUH_last _ g.1 x)
  chr_ext _ g := chr_extTop I.Ch I.sel (I.tup a) (I.cst a) I.Ps g
  tz_ne := by
    have hPr := (base_fields_primes_ok B X).2.1
    show star (((B.primes X).piT u : 𝓞 B.fields.E) : B.fields.E) ≠ 0
    rw [star_ne_zero]
    intro h
    have h1 : (B.primes X).piT u = 0 := RingOfIntegers.ext h
    have h2 := hPr.piT_norm u
    rw [h1, zero_mul] at h2
    exact (hPr.T_prime u).ne_zero (by exact_mod_cast h2.symm)
  Lsh_til b p x := by
    have hPr := (base_fields_primes_ok B X).2.1
    show x ∈ ((I.perIn u a).til b p).1.1.deco.1.Lsh ↔ _
    rw [til_deco h u a b p]
    exact tilH_Lsh _ p.1.1.deco (conj_piT_notMem hPr u) (piT_notMem_vGs hPr u)
      (fun P => decoFin_mem_of_mem_divs P.2) (piT_dvd_of_mem (base_fields_primes_ok B X).1 hPr u) x
  rep_til b p := by
    obtain ⟨d, hd⟩ := (pref_m u a _ _).1 (@pref_prefRep _ _ _ ((I.stp0 u a B.R.m).actD _)
      (I.pref u a B.R.m (idxTop I.sel (I.tup a) (I.idx a))) ((I.perIn u a).til b p) ((pref_m u a _ _).2 ⟨p.1.1, rfl⟩))
    exact ⟨(), trivPt _ _ _ _ _ d, (topPt_val I.sel (I.tup a) (I.cst a) u _).symm.trans
      (congrArg (topPt I.sel (I.tup a) (I.cst a) u) hd)⟩
  H_idx _ := (inferInstance : (⊤ : Subgroup _).FiniteIndex)
  H_rat _ g := ⟨g, Subgroup.mem_top _, rfl⟩

set_option maxHeartbeats 1600000 in

theorem perIn_over (h : I.Ok) (u : B.Word) (a : I.ι) : (I.perIn u a).Over (I.atIn u a) where
  norm_tz := by
    show star (star (((B.primes X).piT u : 𝓞 B.fields.E) : B.fields.E)) *
      star (((B.primes X).piT u : 𝓞 B.fields.E) : B.fields.E) = ((B.primes X).T u : B.fields.E)
    rw [star_star]
    have h := congrArg (algebraMap (𝓞 B.fields.E) B.fields.E) ((base_fields_primes_ok B X).2.1.piT_norm u)
    rw [map_mul, map_natCast] at h
    exact h
  N_til b p x := by
    have hPr := (base_fields_primes_ok B X).2.1
    show x ∈ ((I.perIn u a).til b p).1.1.deco.1.N ↔ _
    rw [til_deco h u a b p]
    exact tilH_N _ p.1.1.deco (conj_piT_notMem hPr u) (piT_notMem_vGs hPr u) x
  f_til b p P x hx := by
    have hPr := (base_fields_primes_ok B X).2.1
    change x ∈ ((I.perIn u a).til b p).1.1.deco.1.N at hx
    show ((I.perIn u a).til b p).1.1.deco.1.f P x = _
    rw [til_deco h u a b p] at hx ⊢
    exact tilH_f _ p.1.1.deco (conj_piT_notMem hPr u) (piT_notMem_vGs hPr u) P x hx

theorem perIn_laws : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok →
    ∀ u a, (I.perIn u a).Ok ∧ (I.perIn u a).Over (I.atIn u a) :=
  fun _ h u a => ⟨perIn_ok h u a, perIn_over h u a⟩

end GlobalTheory.Mem.Col2.PerLaw

end
