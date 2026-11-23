import Formalism.LocalToGlobal.GroupLattices.TiedFamilies.TiePsi
import Formalism.LocalToGlobal.GroupLattices.TiedFamilies.FullTiedCBase

noncomputable section

namespace Formalism.L2.G

open Formalism.L2.G.Cmp Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.L2.Forms Formalism.UG NumberField IsDedekindDomain Matrix
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.BasicNotions.factResChar

section Cast

variable {R : Ranks} {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E]
    [StarRing E] [Algebra F E] {sp : Spaces R F E} {gp : Fin 2 → ℕ}
    {ι' : Type} [Fintype ι'] {hc : ι' → HCParam R} {C : ColumnChain R ι' hc} {A : ColumnsAtT R C}
    {clsLat : ∀ i, C.cls i → Submodule (𝓞 E) (sp.X i).V} {p : ℕ} {G : GAtP p}

theorem levTieOf_yG {L L' : ColLevel R F E sp gp C A clsLat} (h : L' = L) (t : Formalism.L2.Herm.GLevTie L G) :
    (levTieOf h t).yG = t.yG := by
  subst h
  rfl

theorem levTieOf_gamI {L L' : ColLevel R F E sp gp C A clsLat} (h : L' = L) (t : Formalism.L2.Herm.GLevTie L G) :
    (levTieOf h t).gamI = t.gamI := by
  subst h
  rfl

theorem gamToUp_val {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {k : ℕ}
    (σE : E →ₐ[F] E) (J : Matrix (Fin k) (Fin k) E) (Up : Subgroup (GL (Fin k) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)))
    (y : GL (Fin k) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) (γ : gamC σE J Up y) :
    (gamToUp σE J Up y γ : GL (Fin k) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) =
      y⁻¹ * bc (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) (gamMat σE J Up y γ) * y := by
  show (MulAut.conj y⁻¹) (bc (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) (gamMat σE J Up y γ)) = _
  rw [MulAut.conj_apply, inv_inv]

end Cast

def ChiClause {D : D7} {X : Formalism.L2.Herm.Herm0 D} (T : ∀ u : D.what₂.Word, Forms0 D u) (I : CmpIn D X) : Prop :=
  ∀ u w hg i (γ : ((D.gat u w hg).lev i).Γ) (κ : ((T u).cls0).lev.U),
    (locAt X u w hg I.B).IsAway i γ κ.1 →
    ∃ r : D.what₂.LL, D.what₂.embLL r = (((T u).cls0).lev.chi κ : ℂ) ∧
      algebraMap (D.gat u w hg).O (D.gat u w hg).Kf (((D.gat u w hg).lev i).χ γ : (D.gat u w hg).O) * I.embW u w hg r = 1

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

set_option maxHeartbeats 8000000 in

theorem chi_C (H0 : Formalism.L2.Herm.Herm0 (recC D sc Ce Lc I ψ hd)) (hL : ∀ u, H0.lev0 u = Lc u)
    (T : ∀ u : D.what₂.Word, Forms0 (recC D sc Ce Lc I ψ hd) u)
    (B : GL (Fin D.R.k) D.host.E) (hBs : Cmp.StdB (recC D sc Ce Lc I ψ hd) B)
    (hB : ∀ u w hg (w' : HeightOneSpectrum (𝓞 D.host.F)) (h : ((D.what₂.places.resChar w : ℕ) : 𝓞 D.host.F) ∈ w'.asIdeal),
      (I u w hg).fr w' h = bc (((RingHom.fst _ _).comp ((I u w hg).spl w' h).toRingHom).comp
        (inclE (F := D.host.F) (w'.adicCompletion D.host.F))) B)
    (hψ : ∀ u (w : D.what₂.places.Pl) (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)),
      PsiTied (LL := D.what₂.LL) (O := ORec D w (nFr D (D.what₂.places.resChar w)))
        (Kf := KfRec D w (nFr D (D.what₂.places.resChar w)))
        ((T u).cls0).lev (Lc u) (D.what₂.places.resChar w) (rank_eq_first_level D.R) D.what₂.embLL
        ((cmpInC D sc Ce Lc I ψ hd H0 hL B hBs hB).embW u w hg) (ψ u w hg)) :
    ChiClause T (cmpInC D sc Ce Lc I ψ hd H0 hL B hBs hB) := by
  intro u w hg i γ κ hκ
  refine chi_rec (hermitianLevelZeroOfRecursion D sc Ce Lc I ψ hd H0 hL) T u w hg B _ (Lc u) (hL u) (ψ u w hg) ?_ (hψ u w hg) i γ κ hκ
  intro i γ a ha
  have e1 : ((hermitianLevelZeroOfRecursion D sc Ce Lc I ψ hd H0 hL).g u w hg).yG = (levTieG D sc Ce Lc (packC D Lc I ψ) hd u w hg).yG :=
    levTieOf_yG (hL u) _
  have e2 : ((hermitianLevelZeroOfRecursion D sc Ce Lc I ψ hd H0 hL).g u w hg).gamI = (levTieG D sc Ce Lc (packC D Lc I ψ) hd u w hg).gamI :=
    levTieOf_gamI (hL u) _
  rw [e1, e2] at ha
  have e3 : a = gamToUp D.sp.cm.sig D.sp.gram0 (Formalism.L2.Herm.awayFrom₂ (Lc u) (D.what₂.places.resChar w))
      (repP (Lc u) (D.what₂.places.resChar w) i : GL (Fin D.R.k) _) γ :=
    Subtype.ext (ha.trans (gamToUp_val _ _ _ _ γ).symm)
  rw [e3]
  rfl

end Formalism.L2.G
