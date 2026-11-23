import Formalism.LocalToGlobal.GroupLattices.TiedFamilies.FullTiedCBase
import Formalism.LocalToGlobal.GroupLattices.LevelGatherings.PosBridge
import Formalism.LocalToGlobal.GroupLattices.ComparisonMaps.RecThm

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G NumberField IsDedekindDomain Formalism.UG Formalism.L2.Forms Formalism.FrobeniusOrbits

namespace Formalism.L2.G

attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.BasicNotions.factResChar

section Cast

variable {R : Ranks} {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E]
    [StarRing E] [Algebra F E] {sp : Spaces R F E} {gp : Fin 2 → ℕ}
    {ι' : Type} [Fintype ι'] {hc : ι' → HCParam R} {C : ColumnChain R ι' hc} {A : ColumnsAtT R C}
    {clsLat : ∀ i, C.cls i → Submodule (𝓞 E) (sp.X i).V} {p : ℕ} {G : GAtP p}

def tieIw {L : ColLevel R F E sp gp C A clsLat} (t : Formalism.L2.Herm.GLevTie L G) (v : Fin G.P.nV) : E →+* G.P.Qq v :=
  ((t.eQ v _ rfl).symm : (t.pl v).1.adicCompletion F →+* G.P.Qq v).comp
    (((RingHom.fst _ _).comp (t.spl _ (t.pl v).2).toRingHom).comp (inclE (F := F) ((t.pl v).1.adicCompletion F)))

theorem tieIw_levTieOf {L L' : ColLevel R F E sp gp C A clsLat} (h : L' = L) (t : Formalism.L2.Herm.GLevTie L G) :
    tieIw (levTieOf h t) = tieIw t := by
  subst h
  rfl

end Cast

variable (D : D7) (sc : Scale) (Ce : ℝ)
  (Lc : ∀ u, ColLevel D.R D.host.F D.host.E D.sp D.host.g (D.mem u).C (D.mem u).A (D.clsLat u))
  (I : ∀ u (w : D.what₂.places.Pl), GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w) →
    LocId (Lc u) (D.what₂.places.resChar w) (nOrb (zH D.R.toFrame (hP D (D.what₂.places.resChar w))))
      (WQ (D.what₂.places.resChar w) (nFr D (D.what₂.places.resChar w)))
      (QQ (D.what₂.places.resChar w) (nFr D (D.what₂.places.resChar w))))
  (ψ : ∀ u (w : D.what₂.places.Pl), GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w) →
    Formalism.L2.Herm.awayFrom₂ (Lc u) (D.what₂.places.resChar w) →* (ORec D w (nFr D (D.what₂.places.resChar w)))ˣ)
  (hd : ∀ u w h, ((packC D Lc I ψ u w h).gat (rSc sc D.R.k (D.what₂.places.resChar w))
    (epSc D.R sc Ce (D.what₂.places.resChar w))).d = Module.finrank ℂ (D.mem u).A.Mu0)

set_option maxHeartbeats 4000000 in

theorem locAt_iw_C (H0 : Formalism.L2.Herm.Herm0 (recC D sc Ce Lc I ψ hd)) (hL : ∀ u, H0.lev0 u = Lc u)
    (B : GL (Fin D.R.k) D.host.E) (u : D.what₂.Word) (w : D.what₂.places.Pl)
    (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)) (v : Fin (nOrb (zH D.R.toFrame (hP D (D.what₂.places.resChar w)))))
    (x : D.host.E) :
    (Cmp.locAt (hermitianLevelZeroOfRecursion D sc Ce Lc I ψ hd H0 hL) u w hg B).iw v x = (I u w hg).iw v x := by
  show tieIw ((hermitianLevelZeroOfRecursion D sc Ce Lc I ψ hd H0 hL).g u w hg) v x = _
  simp only [hermitianLevelZeroOfRecursion]
  erw [tieIw_levTieOf]
  rfl

set_option maxHeartbeats 4000000 in

theorem pos_C (H0 : Formalism.L2.Herm.Herm0 (recC D sc Ce Lc I ψ hd)) (hL : ∀ u, H0.lev0 u = Lc u)
    (B : GL (Fin D.R.k) D.host.E) (hBs : Cmp.StdB (recC D sc Ce Lc I ψ hd) B)
    (hB : ∀ u w hg (w' : HeightOneSpectrum (𝓞 D.host.F)) (h : ((D.what₂.places.resChar w : ℕ) : 𝓞 D.host.F) ∈ w'.asIdeal),
      (I u w hg).fr w' h = bc (((RingHom.fst _ _).comp ((I u w hg).spl w' h).toRingHom).comp
        (inclE (F := D.host.F) (w'.adicCompletion D.host.F))) B)
    (iK : ∀ u (w : D.what₂.places.Pl), GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w) →
      KfRec D w (nFr D (D.what₂.places.resChar w)) →+* ℂ_[D.what₂.places.resChar w])
    (lam : ∀ u (w : D.what₂.places.Pl), GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w) →
      (algebraicClosure ℚ ℂ) →+* ℂ_[D.what₂.places.resChar w])
    (hK : ∀ u w hg (z : D.what₂.LL), iK u w hg (embRec D w (nFr D (D.what₂.places.resChar w)) z) =
      lamV (lam u w hg) (D.what₂.embLL z))
    (hPos : ∀ u w hg, (packC D Lc I ψ u w hg).posOK (iK u w hg) (lam u w hg))
    (u : D.what₂.Word) (w : D.what₂.places.Pl) (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w))
    (v : Fin (nOrb (zH D.R.toFrame (hP D (D.what₂.places.resChar w))))) (s : Fin (nFr D (D.what₂.places.resChar w))) (x : D.host.E) :
    (cmpInC D sc Ce Lc I ψ hd H0 hL B hBs hB).embW u w hg
        (Cmp.tEL (recC D sc Ce Lc I ψ hd) ((gatTiesC D sc Ce Lc I ψ hd).gat_pos u w hg ⟨v, s⟩)
          (if Even s.val then x else sigD (recC D sc Ce Lc I ψ hd) x)) =
      ((recC D sc Ce Lc I ψ hd).gat u w hg).P.ι v
        ((((recC D sc Ce Lc I ψ hd).gat u w hg).P.σ v ^ s.val)
          ((Cmp.locAt (hermitianLevelZeroOfRecursion D sc Ce Lc I ψ hd H0 hL) u w hg B).iw v x)) := by
  rw [locAt_iw_C D sc Ce Lc I ψ hd H0 hL B u w hg v x]
  apply (iK u w hg).injective
  have h1 := hK u w hg (Cmp.tEL D (D.eTau.symm (posG (zPsi D.R.toFrame (D.R.iota (hP D (D.what₂.places.resChar w)))) ⟨v, s⟩))
    (if Even s.val then x else sigD D x))
  have h2 := hPos u w hg v s x
  have h3 : sigD D x = D.host.conj x := bridge_star_holds D.R D.host x
  have h4 : D.what₂.embLL (Cmp.tEL D (D.eTau.symm (posG (zPsi D.R.toFrame (D.R.iota (hP D (D.what₂.places.resChar w)))) ⟨v, s⟩))
      (if Even s.val then x else sigD D x)) =
      D.host.emb (((posG (zPsi D.R.toFrame (D.R.iota (hP D (D.what₂.places.resChar w)))) ⟨v, s⟩ : D.R.Psi) : D.R.GG) *
        D.R.cc ^ s.val) x := by
    rw [Cmp.tEL_emb, emb_conj_pow]
    unfold embT
    rw [Equiv.apply_symm_apply, h3]
    congr 1
    by_cases hs : s.val % 2 = 1
    · have : ¬ Even s.val := by rw [Nat.not_even_iff_odd, Nat.odd_iff]; exact hs
      simp [hs, this]
    · have : Even s.val := by rw [Nat.even_iff]; omega
      simp [hs, this]
  rw [h4] at h1
  exact h1.trans h2.symm

end Formalism.L2.G
