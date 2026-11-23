import Formalism.LocalToGlobal.GroupLattices.TiedFamilies.TiePtRec
import Formalism.LocalToGlobal.GroupLattices.TiedFamilies.TiePtOne
import Formalism.LocalToGlobal.GroupLattices.TiedFamilies.IntSplitOf

noncomputable section

namespace Formalism.L2.G

open Formalism.L2.G.Cmp Formalism.BasicNotions Formalism.MainNotions.G Formalism.L2.Forms Formalism.UG NumberField IsDedekindDomain Matrix
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.BasicNotions.factResChar

section Gen

variable {R : Ranks} {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E]
    [StarRing E] [Algebra F E] {sp : Spaces R F E} {gp : Fin 2 → ℕ}
    {ι' : Type} [Fintype ι'] {hc : ι' → HCParam R} {C : ColumnChain R ι' hc} {A : ColumnsAtT R C}
    {clsLat : ∀ i, C.cls i → Submodule (𝓞 E) (sp.X i).V} {p : ℕ} {G : GAtP p}

def HypT {L : ColLevel R F E sp gp C A clsLat} (t : Formalism.L2.Herm.GLevTie L G) : Prop :=
  ∀ (w : HeightOneSpectrum (𝓞 F)) (h : ((p : ℕ) : 𝓞 F) ∈ w.asIdeal) (x : GL (Fin R.k) (E ⊗[F] w.adicCompletion F)),
    x ∈ UPts sp.cm.sig sp.gram0 (w.adicCompletion F) →
    (∀ a b, (((t.fr w h)⁻¹ * bc ((RingHom.fst _ _).comp (t.spl w h).toRingHom) x * t.fr w h : GL (Fin R.k) _) :
      Matrix (Fin R.k) (Fin R.k) _) a b ∈ w.adicCompletionIntegers F) →
    (∀ a b, ((((t.fr w h)⁻¹ * bc ((RingHom.fst _ _).comp (t.spl w h).toRingHom) x * t.fr w h)⁻¹ : GL (Fin R.k) _) :
      Matrix (Fin R.k) (Fin R.k) _) a b ∈ w.adicCompletionIntegers F) → x ∈ L.Uloc w

theorem hypT_of {L L' : ColLevel R F E sp gp C A clsLat} (hL : L' = L) (t : Formalism.L2.Herm.GLevTie L' G) {nV : ℕ} {W Qq : Type}
    [CommRing W] [Field Qq] [Algebra W Qq] (I : LocId L p nV W Qq) (hfr : t.fr = I.fr) (hspl : t.spl = I.spl)
    (hH : HypAtP I) : HypT t := by
  subst hL
  intro w h x hx h1 h2
  rw [hfr, hspl] at h1 h2
  obtain ⟨v, rfl⟩ : ∃ v, I.plc v = w := ⟨I.pl.symm ⟨w, h⟩, by simp [LocId.plc]⟩
  exact (hH v x hx).2 ⟨h1, h2⟩

theorem reGL_symm_mem_UPts {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {a b : ℕ} (h : a = b) (σ : E →ₐ[F] E) (J : Matrix (Fin a) (Fin a) E)
    (J' : Matrix (Fin b) (Fin b) E) (hJ : ∀ x y, J' x y = J (Fin.cast h.symm x) (Fin.cast h.symm y))
    (R : Type) [CommRing R] [Algebra F R] (g : GL (Fin b) (E ⊗[F] R)) (hg : g ∈ UPts σ J' R) :
    (reGL h _).symm g ∈ UPts σ J R := by
  subst h
  have : J' = J := by ext x y; exact hJ x y
  rw [this] at hg
  have e : (reGL (rfl : a = a) (E ⊗[F] R)).symm g = g := by
    apply (reGL (rfl : a = a) (E ⊗[F] R)).injective
    rw [MulEquiv.apply_symm_apply, reGL_rfl]
  rw [e]; exact hg

end Gen

variable {D : D7} (X : Formalism.L2.Herm.Herm0 D)

theorem locInt_locAt (u : D.what₂.Word) (w : D.what₂.places.Pl) (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w))
    (B : GL (Fin D.R.k) D.host.E) : LocInt (locAt X u w hg B) :=
  fun v x => (X.g u w hg).completion_integers_iff v _ rfl x

set_option maxHeartbeats 4000000 in
theorem locHyp_locAt (T : ∀ u : D.what₂.Word, Forms0 D u) (u : D.what₂.Word) (hU : SameUloc X T u) (w : D.what₂.places.Pl)
    (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)) (B : GL (Fin D.R.k) D.host.E) (hB : FrRat X u w hg B)
    (hT : HypT (X.g u w hg)) : LocHyp ((T u).cls0).lev (locAt X u w hg B) := by
  refine locHyp_of (rank_eq_first_level D.R) (locAt X u w hg B) _ D.sp.gram0 (gramN_zero D) B rfl
    (fun v => (X.lev0 u).Uloc v) hU ?_
  intro v x0 hx0 h1 h2
  have hfr := hB _ ((X.g u w hg).pl v).2
  refine hT _ ((X.g u w hg).pl v).2 x0 hx0 ?_ ?_
  · rw [hfr]; exact h1
  · rw [hfr]; exact h2

theorem bad_notOver (u : D.what₂.Word) (w : D.what₂.places.Pl) (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w))
    (w' : HeightOneSpectrum (𝓞 D.host.F)) (hw : w' ∈ badG D) : ((D.what₂.places.resChar w : ℕ) : 𝓞 D.host.F) ∉ w'.asIdeal := by
  intro hv
  have hp : (D.what₂.places.resChar w).Prime := hg.1
  have hg' : ∀ i, ¬ D.what₂.places.resChar w ∣ D.host.g i := fun i hd =>
    hg.2.2.2.2.1 (((Nat.prime_dvd_prime_iff_eq hp (D.host.g_prime i)).1 hd) ▸ D.host.g_level i)
  rcases hw with h | h
  · exact natCast_notMem _ hp hv (hg' 0) h
  · exact natCast_notMem _ hp hv (hg' 1) h

set_option maxHeartbeats 4000000 in

theorem ptOne_rec (T : ∀ u : D.what₂.Word, Forms0 D u) (u : D.what₂.Word) (hU : SameUloc X T u) (w : D.what₂.places.Pl)
    (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)) (B : GL (Fin D.R.k) D.host.E) (hB : FrRat X u w hg B)
    (hT : HypT (X.g u w hg)) : PtOne ((T u).cls0).lev (D.gat u w hg) (locAt X u w hg B) :=
  ptOne_of _ (locInt_locAt X u w hg B) (locHyp_locAt X T u hU w hg B hB hT)
    (bad_notOver u w hg)

end Formalism.L2.G
