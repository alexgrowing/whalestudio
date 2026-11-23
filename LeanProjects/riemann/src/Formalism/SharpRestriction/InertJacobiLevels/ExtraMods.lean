import Formalism.SharpRestriction.InertJacobiLevels.GaugeExists
import Formalism.SharpRestriction.InertJacobiLevels.ExtraGatC
import Formalism.SharpRestriction.InertJacobiLevels.ExtraH
import Formalism.LocalRingCardinality.SpanPowerMembership.WithSeenTauOf

noncomputable section

namespace Formalism.MainNotions.Inhab

open Formalism.BasicNotions Formalism.BasicNotions.Examples₂ Formalism.MainNotions NumberField IsDedekindDomain

structure Shape0 (D : D7) : Prop where
  mult : ∀ μ j, Subsingleton (D.what₂.Mult μ j)
  amb : ∀ μ, Subsingleton (D.what₂.Amb μ)
  mtL : ∀ μ j, Subsingleton (D.what₂.MtL μ j)
  mj : ∀ j, Subsingleton (D.what₂.Mj j)
  ee0 : Subsingleton D.what₂.EE0
  rr : Subsingleton D.div.RR.V
  nu : ∀ u, Subsingleton (D.div.Nu u).V
  lat : ∀ u j, Subsingleton ((D.fm u).lat j).V
  yTw : ∀ u μ i, IsEmpty ((D.chTw u μ).Y i)
  clsTw : ∀ u μ j, IsEmpty ((D.chTw u μ).cls (j + 1))
  mtV : ∀ i j b k Q ψ, Subsingleton (D.nexp.MtV i j b k Q ψ)
  fmN : ∀ i j b, Subsingleton (D.nexp.Fm i j b)
  ll0 : ∀ x : D.what₂.LL, x ∈ D.LL0
  Ij0 : ∀ μ j w, D.what₂.Ij μ j w = 0
  jw0 : ∀ μ j w, D.what₂.jw μ j w = 0
  drows : D.what₂.Drows = 0
  dgam : ∀ u μ, (D.chTw u μ).DGam = (D.mem D.u₀).C.DGam
  mink : DGamMink D
  loc : IsEmpty D.nd.Loc
  cls0 : ∀ u μ, Nonempty ((D.mem u).C.cls 0 ≃ (D.chTw u μ).cls 0)

variable {D : D7}

theorem Shape0.withGat (S : Shape0 D) (h0 : ∀ u, Module.finrank ℂ (D.mem u).A.Mu0 = 0)
    (rOf : D.what₂.Word → ℕ → ℕ) (eOf : ℕ → ℕ) (bs : D.what₂.Word → ℕ → Set ↥(D.R.Psi)) :
    Shape (withGatC D h0 rOf eOf bs) where
  mult := S.mult
  amb := S.amb
  mtL := S.mtL
  mj := S.mj
  ee0 := S.ee0
  rr := S.rr
  nu := S.nu
  lat := S.lat
  yTw := S.yTw
  clsTw := S.clsTw
  mtV := S.mtV
  fmN := S.fmN
  ll0 := S.ll0
  Ij0 := S.Ij0
  jw0 := S.jw0
  drows := S.drows
  dgam := S.dgam
  mink := S.mink
  loc := S.loc
  gatM := withGatC_M D h0 rOf eOf bs
  gatComp := fun u w _ => S.cls0 u (D.what₂.muAt w)
  gatTr := withGatC_trans D h0 rOf eOf bs

theorem Shape0.withSeen (S : Shape0 D) (seen tau) : Shape0 (withSeen D seen tau) where
  mult := S.mult
  amb := S.amb
  mtL := S.mtL
  mj := S.mj
  ee0 := S.ee0
  rr := S.rr
  nu := S.nu
  lat := S.lat
  yTw := S.yTw
  clsTw := S.clsTw
  mtV := S.mtV
  fmN := S.fmN
  ll0 := S.ll0
  Ij0 := S.Ij0
  jw0 := S.jw0
  drows := S.drows
  dgam := S.dgam
  mink := S.mink
  loc := S.loc
  cls0 := S.cls0

structure LevGapD (D : D7) where
  lev : LevelData D
  errX : ErrX D
  piG_lev : PiGLevel D lev errX
  piT_lev : PiTLevel D lev errX
  tau : ∀ u, D.what₂.places.Pl → ((D.mem u).A.vT ≃ D.what₂.Tau)
  tau_def : ∀ u (w : D.what₂.places.Pl), D.what₂.places.resChar w = (D.mem u).A.T → ∀ (v : (D.mem u).A.vT)
    (x : 𝓞 D.host.F), x ∈ (errX.vPl u v).asIdeal ↔
      (0 : WithTop ℤ) < D.what₂.places.val w (tauLL D (tau u w v) (algebraMap D.host.F D.host.E (x : D.host.F)))

open Classical in

def seenOf (D : D7) (X : ErrX D) : D.what₂.Word → D.what₂.places.Pl → Bool :=
  fun u w => decide (∀ τ : D.what₂.Tau, (0 : WithTop ℤ) < D.what₂.places.val w (tauLL D τ (X.piT u : D.host.E)))

def LevGapD.recS (G : LevGapD D) : D7 := withSeen D (seenOf D G.errX) G.tau

def errXSeen (X : ErrX D) (seen tau) : ErrX (withSeen D seen tau) where
  piG := X.piG
  piG_K := X.piG_K
  piG_norm := X.piG_norm
  piT := X.piT
  piT_K := X.piT_K
  piT_norm := X.piT_norm
  piT_cong := X.piT_cong
  vPl := X.vPl
  vPl_inj := X.vPl_inj
  norm_mem_place_ideal := X.norm_mem_place_ideal

def LevGapD.le (G : LevGapD D) : LevErr G.recS where
  lev := G.lev
  errX := errXSeen G.errX _ _
  piG_lev := G.piG_lev
  piT_lev := G.piT_lev
  seen := fun u w _ => by
    show seenOf D G.errX u w = true ↔ _
    unfold seenOf
    rw [decide_eq_true_iff]
    rfl
  tauOf := G.tau_def

section LevelValuationRings

variable (h0 : ∀ u, Module.finrank ℂ (D.mem u).A.Mu0 = 0)
    (rOf : D.what₂.Word → ℕ → ℕ) (eOf : ℕ → ℕ) (bs : D.what₂.Word → ℕ → Set ↥(D.R.Psi))

def errXGat (X : ErrX D) : ErrX (withGatC D h0 rOf eOf bs) where
  piG := X.piG
  piG_K := X.piG_K
  piG_norm := X.piG_norm
  piT := X.piT
  piT_K := X.piT_K
  piT_norm := X.piT_norm
  piT_cong := X.piT_cong
  vPl := X.vPl
  vPl_inj := X.vPl_inj
  norm_mem_place_ideal := X.norm_mem_place_ideal

def LevErr.withGat (le : LevErr D) : LevErr (withGatC D h0 rOf eOf bs) where
  lev := le.lev
  errX := errXGat h0 rOf eOf bs le.errX
  piG_lev := le.piG_lev
  piT_lev := le.piT_lev
  seen := le.seen
  tauOf := le.tauOf

variable (B : D.what₂.Word → ℕ → Set (G.HH D))

theorem Shape0.withGatB (S : Shape0 D) : Shape (withGatCB D h0 rOf eOf B) := S.withGat h0 rOf eOf _

def LevErr.withGatB (le : LevErr D) : LevErr (withGatCB D h0 rOf eOf B) := LevErr.withGat h0 rOf eOf _ le

end LevelValuationRings

theorem LevGapD.shape0 (large₂ : LevGapD D) (S : Shape0 D) : Shape0 large₂.recS := S.withSeen _ _

def ServedGap : Prop :=
  ∀ (D : D7), Function.Bijective D.embE → ∀ (h0 : ∀ u, Module.finrank ℂ (D.mem u).A.Mu0 = 0)
    (rOf : D.what₂.Word → ℕ → ℕ) (eOf : ℕ → ℕ) (bs : D.what₂.Word → ℕ → Set ↥(D.R.Psi))
    (u : D.what₂.Word) (w : D.what₂.places.Pl) (h : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)),
    haveI : Fact ((withGatC D h0 rOf eOf bs).what₂.places.resChar w).Prime := ⟨D.what₂.places.resChar_prime w⟩
    Nonempty (ServedEmb (withGatC D h0 rOf eOf bs) u w h)

def GaugeGap : Prop :=
  ∀ (R : Ranks) (H : Host R) (sp : @Spaces R H.F H.E _ _ _ _ H.cmStar _), GaugeExists H sp

end Formalism.MainNotions.Inhab

end
