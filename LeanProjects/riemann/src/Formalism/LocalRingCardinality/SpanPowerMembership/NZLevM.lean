import Formalism.LocalRingCardinality.SpanPowerMembership.NZLevL
import Formalism.LocalRingCardinality.SpanPowerMembership.NZColA

noncomputable section

namespace Formalism.BasicNotions.Examples₂.NZ

open Formalism.BasicNotions Formalism.BasicNotions.Examples₂ Formalism.BasicNotions.Examples₂.LevelValuationRings Formalism.MainNotions.G Formalism.FrobeniusOrbits NumberField Formalism.MainNotions.Inhab

section One

variable {R : Ranks} {H : Host R} {p : ℕ}

theorem charZero_Kn (S : Served H p) :
    haveI : Fact p.Prime := ⟨S.prime⟩
    CharZero (Kn p (orderOf (gPsi S))) :=
  haveI : Fact p.Prime := ⟨S.prime⟩
  charZero_of_setting (hidaSettingOfEven p _ S.five_le (ord_spec S).2.1 (ord_spec S).2.2)

theorem p_ne_Kn (S : Served H p) :
    haveI : Fact p.Prime := ⟨S.prime⟩
    ((p : ℕ) : Kn p (orderOf (gPsi S))) ≠ 0 :=
  haveI : Fact p.Prime := ⟨S.prime⟩
  haveI := charZero_Kn S
  Nat.cast_ne_zero.mpr S.prime.ne_zero

theorem nOrb_pos (S : Served H p) : 0 < nOrb S := Nat.card_pos

def gatNZ (S : Served H p) (T : Set ↥(R.Psi)) (r : ℕ) (lam : ↥(R.Psi) → DomWeight (R.N 0))
    (comp : Type) [Fintype comp] (e : ℕ) : GAtP p :=
  haveI : Fact p.Prime := ⟨S.prime⟩
  haveI := charZero_Kn S
  { O := On p (orderOf (gPsi S))
    Kf := Kn p (orderOf (gPsi S))
    P := placesOf S T r lam
    comp := comp
    lev := fun _ => levB (placesOf S T r lam) (p_ne_Kn S)
    e := e }

theorem gatNZ_eq (S : Served H p) (T : Set ↥(R.Psi)) (r : ℕ) (lam : ↥(R.Psi) → DomWeight (R.N 0))
    (comp : Type) [Fintype comp] [DecidableEq comp] (e : ℕ) :
    haveI : Fact p.Prime := ⟨S.prime⟩
    haveI := charZero_Kn S
    (gatNZ S T r lam comp e).M = (gatC (placesOf S T r lam) (p_ne_Kn S) comp).M := rfl

theorem gatNZ_d (S : Served H p) (T : Set ↥(R.Psi)) (r : ℕ) (lam : ↥(R.Psi) → DomWeight (R.N 0))
    (comp : Type) [Fintype comp] [DecidableEq comp] (e : ℕ) : (gatNZ S T r lam comp e).d = Fintype.card comp := by
  haveI : Fact p.Prime := ⟨S.prime⟩
  haveI := charZero_Kn S
  exact gatC_d (placesOf S T r lam) (p_ne_Kn S) comp ⟨0, nOrb_pos S⟩

def FbNZ (S : Served H p) (T : Set ↥(R.Psi)) (r : ℕ) (lam : ↥(R.Psi) → DomWeight (R.N 0))
    (comp : Type) [Fintype comp] [DecidableEq comp] (e : ℕ) (c : comp) : (gatNZ S T r lam comp e).Fn :=
  haveI : Fact p.Prime := ⟨S.prime⟩
  haveI := charZero_Kn S
  Fb (placesOf S T r lam) (p_ne_Kn S) comp c

theorem FbNZ_li (S : Served H p) (T : Set ↥(R.Psi)) (r : ℕ) (lam : ↥(R.Psi) → DomWeight (R.N 0))
    (comp : Type) [Fintype comp] [DecidableEq comp] (e : ℕ) :
    LinearIndependent (gatNZ S T r lam comp e).Kf (FbNZ S T r lam comp e) := by
  haveI : Fact p.Prime := ⟨S.prime⟩
  haveI := charZero_Kn S
  exact Fb_li (placesOf S T r lam) (p_ne_Kn S) comp ⟨0, nOrb_pos S⟩

theorem FbNZ_span (S : Served H p) (T : Set ↥(R.Psi)) (r : ℕ) (lam : ↥(R.Psi) → DomWeight (R.N 0))
    (comp : Type) [Fintype comp] [DecidableEq comp] (e : ℕ) :
    Submodule.span (gatNZ S T r lam comp e).O (Set.range (FbNZ S T r lam comp e)) = (gatNZ S T r lam comp e).M := by
  haveI : Fact p.Prime := ⟨S.prime⟩
  haveI := charZero_Kn S
  exact M_eq (placesOf S T r lam) (p_ne_Kn S) comp ⟨0, nOrb_pos S⟩

end One

open Classical in

def withGatNZ (D : D7) (h1 : ∀ u, Module.finrank ℂ (D.mem u).A.Mu0 = Fintype.card ((D.mem u).C.cls 0))
    (rOf : D.what₂.Word → ℕ → ℕ) (eOf : ℕ → ℕ) (bs : D.what₂.Word → ℕ → Set ↥(D.R.Psi)) : D7 :=
  { D with
    gat := fun u w h => gatNZ (served_of h) (bs u (D.what₂.places.resChar w))
      (rOf u (D.what₂.places.resChar w)) (fun ψ => (D.fm u).lam 0 (D.eTau.symm ψ)) ((D.mem u).C.cls 0)
      (eOf (D.what₂.places.resChar w))
    gat_d := fun u _ _ => (gatNZ_d _ _ _ _ _ _).trans (h1 u).symm }

variable (D : D7) (h1 : ∀ u, Module.finrank ℂ (D.mem u).A.Mu0 = Fintype.card ((D.mem u).C.cls 0))
  (rOf : D.what₂.Word → ℕ → ℕ) (eOf : ℕ → ℕ) (bs : D.what₂.Word → ℕ → Set ↥(D.R.Psi))

def gatTiesNZ : GatTies (withGatNZ D h1 rOf eOf bs) where
  gat_k := fun _ _ _ => k_pos D.R
  gat_n := fun _ _ h _ P hP hL σ hσ => @orderOf_frobenius_image_eq _ D.host _ (served_of h) P hP hL σ hσ
  gat_pos := fun u w h => (posPsi (served_of h) (bs u (D.what₂.places.resChar w))).trans D.eTau.symm
  gat_step := fun u w h v s P hP hL σ hσ =>
    @position_succ_eq_mul_frobenius _ D.host _ (served_of h) (bs u (D.what₂.places.resChar w)) _ D.eTau v s P hP hL σ hσ
  gat_lam := fun _ _ _ _ _ _ => rfl

theorem withGatNZ_d (u w h) : ((withGatNZ D h1 rOf eOf bs).gat u w h).d = Fintype.card ((D.mem u).C.cls 0) := by
  classical
  exact gatNZ_d _ _ _ _ _ _

open Classical in

def gatBasisNZ
    (eι : ∀ u, ((D.fm u).lat 0).ι ≃ (D.mem u).C.cls 0)
    (embW : ∀ u (w : D.what₂.places.Pl) (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)),
      D.what₂.LL →+* ((withGatNZ D h1 rOf eOf bs).gat u w hg).Kf)
    (embW_int : ∀ u w hg (x : D.what₂.LL), (0 : WithTop ℤ) ≤ D.what₂.places.val w x ↔
      embW u w hg x ∈ Set.range (algebraMap ((withGatNZ D h1 rOf eOf bs).gat u w hg).O
        ((withGatNZ D h1 rOf eOf bs).gat u w hg).Kf)) :
    GatBasis (withGatNZ D h1 rOf eOf bs) where
  embW := embW
  embW_int := embW_int
  bas u w hg a := FbNZ (served_of hg) _ _ _ ((D.mem u).C.cls 0) _ (eι u a)
  bas_li u w hg := (FbNZ_li (served_of hg) _ _ _ ((D.mem u).C.cls 0) _).comp _ (eι u).injective
  bas_span u w hg := by
    refine Eq.trans ?_ (FbNZ_span (served_of hg) _ _ _ ((D.mem u).C.cls 0) _)
    congr 1
    ext x; constructor
    · rintro ⟨a, rfl⟩; exact ⟨eι u a, rfl⟩
    · rintro ⟨c, rfl⟩
      refine ⟨(eι u).symm c, ?_⟩
      simp only [Equiv.apply_symm_apply]
      congr

end Formalism.BasicNotions.Examples₂.NZ
