import Formalism.LocalToGlobal.GroupLattices.ComparisonMaps.CmpCMemFunMod
import Formalism.LocalToGlobal.GroupLattices.ComparisonMaps.RecThm
import Formalism.LocalToGlobal.GroupLattices.ComparisonMaps.SpanImageOfSurj

noncomputable section

namespace Formalism.L2.G.Cmp

open Formalism.MainNotions.G Formalism.BasicNotions Formalism.L2.Forms Formalism.UG NumberField IsDedekindDomain Matrix
open scoped TensorProduct

section Gen

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {T f : ℕ} {bad : Set (HeightOneSpectrum (𝓞 F))}
  {Tau : Type} [Fintype Tau] {LL : Type} [Field LL] {p : ℕ}
  (S : StepLevel F E σ J T f bad) (emb : Tau → E →+* ℂ) (embLL : LL →+* ℂ)
  (G : GAtP p) (e : LL →+* G.Kf) (A : LocAt F E n G) (pos : (Σ v : Fin G.P.nV, Fin (G.P.n' v)) ≃ Tau)
  {V cls : Type} [AddCommGroup V] [Module LL V] (embV : V →ₛₗ[embLL] (cls → Frames (gramC J emb) → ℂ))
  (yc : cls → UPts σ J (FiniteAdeleRing (𝓞 F) F))

def PtRel (i : G.comp) (L : G.P.Tup) (c : cls) : Prop :=
  ∃ (g : ∀ v, GL (Fin (G.P.m + 1)) (G.P.Qq v)) (γ : GL (Fin n) E) (κ : S.U),
    (∀ v, L v = colSpan (G.P.W v) (g v : Matrix (Fin (G.P.m + 1)) (Fin (G.P.m + 1)) (G.P.Qq v))) ∧
    γ ∈ UJ (σ : E →+* E) J ∧ A.IsPt i g (bc (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) γ * (yc c).1 * κ.1)

def ValIntAt (IntAt : V → cls → Prop) : Prop :=
  ∀ (x : V) (i : G.comp) (L : G.P.Tup) (c : cls), G.P.IsLatTup L → PtRel S G A yc i L c →
    (cmpC S emb embLL G e A pos embV yc x i L ∈ G.P.HtupW L ↔ IntAt x c)

variable {S emb embLL G e A pos embV yc}

theorem exists_bases {L : G.P.Tup} (hL : G.P.IsLatTup L) :
    ∃ g : ∀ v, GL (Fin (G.P.m + 1)) (G.P.Qq v),
      ∀ v, L v = colSpan (G.P.W v) (g v : Matrix (Fin (G.P.m + 1)) (Fin (G.P.m + 1)) (G.P.Qq v)) := by
  have hL' : ∀ v, ∃ g : Matrix (Fin (G.P.m + 1)) (Fin (G.P.m + 1)) (G.P.Qq v),
      IsUnit g.det ∧ L v = colSpan (G.P.W v) g := hL
  choose g hg using hL'
  refine ⟨fun v => ((Matrix.isUnit_iff_isUnit_det (g v)).mpr (hg v).1).unit, fun v => ?_⟩
  rw [IsUnit.unit_spec]
  exact (hg v).2

theorem cmpC_mem_M_iff (tE : Tau → E →+* LL) (htE : ∀ τ x, embLL (tE τ x) = emb τ x)
    (hc : ∀ τ x, emb τ (σ x) = starRingEnd ℂ (emb τ x)) (hBs : cT (σ : E →+* E) A.B.1 * J * A.B.1 = 1) (hA : A.ActB)
    (hex : ValEx S emb embLL G A pos embV yc)
    (hpos : ∀ v (s : Fin (G.P.n' v)) (x : E),
      e (tE (pos ⟨v, s⟩) (if Even s.val then x else σ x)) = G.P.ι v ((G.P.σ v ^ s.val) (A.iw v x)))
    (hchi : ∀ i (γ : (G.lev i).Γ) (κ : S.U), A.IsAway i γ κ.1 →
      ∃ r : LL, embLL r = (S.chi κ : ℂ) ∧ algebraMap G.O G.Kf ((G.lev i).χ γ : G.O) * e r = 1)
    (hi : EvInj emb G A pos (J := J)) (hp : PtEx S G A yc) (hall : PtAll S G A yc)
    (hU : ∀ i (γ : (G.lev i).Γ), A.gamI i γ ∈ UJ (σ : E →+* E) J)
    (haw : ∀ i (γ : (G.lev i).Γ), ∃ κ : S.U, A.IsAway i γ κ.1)
    (IntAt : V → cls → Prop) (hloc : ValIntAt S emb embLL G e A pos embV yc IntAt) (x : V) :
    cmpC S emb embLL G e A pos embV yc x ∈ G.M ↔ ∀ c, IntAt x c := by
  constructor
  · intro hM c
    obtain ⟨i, g, γ, κ, hγ, hpt⟩ := hall c
    let L : G.P.Tup := fun v => colSpan (G.P.W v) (g v : Matrix (Fin (G.P.m + 1)) (Fin (G.P.m + 1)) (G.P.Qq v))
    have hL : G.P.IsLatTup L := fun v => ⟨_, (Matrix.isUnit_iff_isUnit_det _).1 (g v).isUnit, rfl⟩
    have hv : cmpC S emb embLL G e A pos embV yc x i L ∈ G.P.HtupW L :=
      ((mem_funMod_iff G G.P.HtupW _).1 hM i).1 L hL
    exact (hloc x i L c hL ⟨g, γ, κ, fun _ => rfl, hγ, hpt⟩).1 hv
  · intro hI
    refine cmpC_mem_funMod tE htE hc hBs hA hex hpos hchi hi hp hU haw G.P.HtupW x fun i L hL => ?_
    obtain ⟨g, hg⟩ := exists_bases hL
    obtain ⟨c, γ, κ, hγ, hpt⟩ := hp i g
    have h1 := (hloc x i L c hL ⟨g, γ, κ, hg, hγ, hpt⟩).2 (hI c)
    unfold cmpC at h1
    rwa [if_pos hL] at h1

end Gen

section Rec

variable {D : D7} {X : Formalism.L2.Herm.Herm0 D}

def IntAtW (T : ∀ u : D.what₂.Word, Forms0 D u) (u : D.what₂.Word) (w : D.what₂.places.Pl)
    (x : ((D.fm u).lat 0).V) (c : (D.mem u).C.cls 0) : Prop :=
  ∀ B : GL (Fin (D.R.N 0)) D.host.E,
    Formalism.L2.Forms.IsLocBasis (D.what₂.places.resChar w)
      (dualSet (sigD D : D.host.E →+* D.host.E) (gramN D 0 (Nat.zero_le _)) (clsCrd D u 0 (Nat.zero_le _) c)) B →
    ∃ P ∈ IntSpan D w ((D.fm u).lam 0),
      ∀ z, (D.fm u).emb 0 x c z =
        fnOf _ (shiftOf (lamT u 0)) (atInf (embT D) (B⁻¹ : GL (Fin (D.R.N 0)) D.host.E).1) P
          (((T u).val0).eY z)

def ValIntRec (T : ∀ u : D.what₂.Word, Forms0 D u) (Gt : GatTies D) (I : CmpIn D X) : Prop :=
  ∀ u w hg, ValIntAt ((T u).cls0).lev (embT D) D.what₂.embLL (D.gat u w hg) (I.embW u w hg)
    (locAt X u w hg I.B) (Gt.gat_pos u w hg) (embFr T u) ((T u).cls0).y (IntAtW T u w)

def LocWCrit (T : ∀ u : D.what₂.Word, Forms0 D u) : Prop :=
  ∀ u (w : D.what₂.places.Pl) (x : ((D.fm u).lat 0).V),
    x ∈ locW D.what₂.places w ((D.fm u).lat 0).L ↔ ∀ c, IntAtW T u w x c

def LocWBack (T : ∀ u : D.what₂.Word, Forms0 D u) : Prop :=
  ∀ u (w : D.what₂.places.Pl) (x : ((D.fm u).lat 0).V),
    (∀ c, IntAtW T u w x c) → x ∈ locW D.what₂.places w ((D.fm u).lat 0).L

theorem intSpan_smul (w : D.what₂.places.Pl) {n : ℕ} (lam : D.what₂.Tau → DomWeight n) (a : D.what₂.LL)
    (ha : a ∈ intW D.what₂.places w) {P : MvPolynomial (D.what₂.Tau × Fin n × Fin n) ℂ} (hP : P ∈ IntSpan D w lam) :
    D.what₂.embLL a • P ∈ IntSpan D w lam := by
  unfold IntSpan at hP ⊢
  induction hP using AddSubgroup.closure_induction with
  | mem p hp =>
    obtain ⟨r, f, hr, hf, rfl⟩ := hp
    refine AddSubgroup.subset_closure ⟨a * r, f, mul_mem ha hr, hf, ?_⟩
    rw [map_mul, mul_smul]
  | zero =>
    rw [smul_zero]
    exact zero_mem _
  | add p q _ _ hp hq =>
    rw [smul_add]
    exact add_mem hp hq
  | neg p _ hp =>
    rw [smul_neg]
    exact neg_mem hp

theorem locW_intAtW (T : ∀ u : D.what₂.Word, Forms0 D u) (u : D.what₂.Word) (w : D.what₂.places.Pl)
    (x : ((D.fm u).lat 0).V) (hx : x ∈ locW D.what₂.places w ((D.fm u).lat 0).L) (c : (D.mem u).C.cls 0) :
    IntAtW T u w x c := by
  induction hx using Submodule.span_induction with
  | mem y hy =>
    intro B hB
    exact (((T u).val0).lat y).1 hy w c B hB
  | zero =>
    intro B _
    refine ⟨0, AddSubgroup.zero_mem _, fun z => ?_⟩
    rw [map_zero, map_zero]
    rfl
  | add y z _ _ h1 h2 =>
    intro B hB
    obtain ⟨P, hP, hPy⟩ := h1 B hB
    obtain ⟨Q, hQ, hQz⟩ := h2 B hB
    refine ⟨P + Q, AddSubgroup.add_mem _ hP hQ, fun t => ?_⟩
    rw [map_add, map_add]
    show (D.fm u).emb 0 y c t + (D.fm u).emb 0 z c t = _
    rw [hPy t, hQz t]
    rfl
  | smul a y _ h1 =>
    intro B hB
    obtain ⟨P, hP, hPy⟩ := h1 B hB
    refine ⟨D.what₂.embLL a.1 • P, intSpan_smul w _ a.1 a.2 hP, fun t => ?_⟩
    rw [Subring.smul_def, LinearMap.map_smulₛₗ, map_smul]
    show D.what₂.embLL a.1 * (D.fm u).emb 0 y c t = _
    rw [hPy t]
    rfl

theorem locWCrit_of (T : ∀ u : D.what₂.Word, Forms0 D u) (h : LocWBack T) : LocWCrit T :=
  fun u w x => ⟨fun hx c => locW_intAtW T u w x hx c, h u w x⟩

end Rec

end Formalism.L2.G.Cmp
