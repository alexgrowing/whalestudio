import Formalism.LocalToGlobal.GroupLattices.TiedFamilies.TieStd
import Formalism.LocalToGlobal.GroupLattices.TiedFamilies.IntSplitOf
import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.LocIdFr
import Formalism.LocalToGlobal.HermitianForms.BothLemmas

noncomputable section

open Formalism.BasicNotions Formalism.L2.Forms Formalism.UG NumberField IsDedekindDomain Matrix
open scoped TensorProduct

namespace Formalism.L2.G

section Re

theorem reGL_mulVec {a b : ℕ} (h : a = b) {E : Type} [Field E] (M : GL (Fin a) E) (x : Fin a → E) (i : Fin b) :
    ((reGL h E M).1 *ᵥ fun j : Fin b => x (Fin.cast h.symm j)) i = (M.1 *ᵥ x) (Fin.cast h.symm i) := by
  subst h
  rw [reGL_rfl]
  rfl

end Re

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem stdB_mem (D : D7) (B : GL (Fin D.R.k) D.host.E) (hB : Cmp.StdB D B) (x : Fin D.R.k → D.host.E) :
    x ∈ D.sp.crdLat0 (D.sp.X 0).L0 ↔
      ∀ a, ((B⁻¹ : GL (Fin D.R.k) D.host.E).1 *ᵥ x) a ∈ (algebraMap (𝓞 D.host.E) D.host.E).range := by
  have h2 := hB.2 (fun j => x (Fin.cast (rank_eq_first_level D.R).symm j))
  have e1 : (fun j => x (Fin.cast (rank_eq_first_level D.R).symm j)) ∈ selfDualLatticeCoords D 0 (Nat.zero_le _) ↔ x ∈ D.sp.crdLat0 (D.sp.X 0).L0 := by
    constructor
    · rintro ⟨v, hv, e⟩
      refine ⟨v, hv, ?_⟩
      funext a
      have := congrFun e (Fin.cast (rank_eq_first_level D.R) a)
      exact this
    · rintro ⟨v, hv, e⟩
      refine ⟨v, hv, ?_⟩
      funext j
      have := congrFun e (Fin.cast (rank_eq_first_level D.R).symm j)
      exact this
  rw [← e1, h2]
  constructor
  · intro h a
    have := h (Fin.cast (rank_eq_first_level D.R) a)
    rw [← map_inv, reGL_mulVec] at this
    exact this
  · intro h j
    rw [← map_inv, reGL_mulVec]
    exact h _

variable {R : Ranks} {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E]
    [StarRing E] [Algebra F E] {sp : Spaces R F E} {gp : Fin 2 → ℕ}
    {ι' : Type} [Fintype ι'] {hc : ι' → HCParam R} {C : ColumnChain R ι' hc} {A : ColumnsAtT R C}
    {clsLat : ∀ i, C.cls i → Submodule (𝓞 E) (sp.X i).V}
    {L : ColLevel R F E sp gp C A clsLat} {p nV : ℕ} {W Qq : Type} [CommRing W] [Field Qq] [Algebra W Qq]

theorem T_smul_mem (L : ColLevel R F E sp gp C A clsLat) (y : Fin R.k → E)
    (hy : y ∈ Submodule.span (𝓞 E) (dualSet (sp.cm.sig : E →+* E) sp.gram0 L.Lb)) : (A.T : E) • y ∈ L.Lb := by
  induction hy using Submodule.span_induction with
  | mem y hy => exact L.Lb_dual y hy
  | zero => rw [smul_zero]; exact L.Lb.zero_mem
  | add y z _ _ h1 h2 => rw [smul_add]; exact L.Lb.add_mem h1 h2
  | smul c y _ h => rw [smul_comm]; exact L.Lb.smul_mem c h

theorem companion_le (L : ColLevel R F E sp gp C A clsLat) (𝔞 : Ideal (𝓞 E)) :
    L.Lb ⊔ 𝔞 • Submodule.span (𝓞 E) (dualSet (sp.cm.sig : E →+* E) sp.gram0 L.Lb) ≤
      Submodule.span (𝓞 E) (dualSet (sp.cm.sig : E →+* E) sp.gram0 L.Lb) :=
  sup_le (fun x hx => Submodule.subset_span (L.Lb_int x hx)) Submodule.smul_le_right

def LocId.withFr (I : LocId L p nV W Qq) (B : GL (Fin R.k) E)
    (h1 : ∀ x ∈ L.Lb, ∀ a, ((B⁻¹ : GL (Fin R.k) E).1 *ᵥ x) a ∈ (algebraMap (𝓞 E) E).range)
    (N : ℕ) (hN : ∀ w : HeightOneSpectrum (𝓞 F), ((p : ℕ) : 𝓞 F) ∈ w.asIdeal → (N : 𝓞 F) ∉ w.asIdeal)
    (h2 : ∀ i, (N : E) • (B.1 *ᵥ Pi.single i 1) ∈ L.Lb) : LocId L p nV W Qq :=
  { I with
    fr := fun w h => bc (((RingHom.fst _ _).comp (I.spl w h).toRingHom).comp (inclE (F := F) (w.adicCompletion F))) B
    fr_lat := fun w h t => Formalism.MainNotions.Gaps.Loc.fr_lat_of w (I.spl w h) (I.spl_alg w h) L.Lb B h1 N (hN w h) h2 t }

def locIdStd (D : D7) (u : D.what₂.Word) (w : D.what₂.places.Pl) (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w))
    {Lc : ColLevel D.R D.host.F D.host.E D.sp D.host.g (D.mem u).C (D.mem u).A (D.clsLat u)} {nV : ℕ} {W' Qq' : Type}
    [CommRing W'] [Field Qq'] [Algebra W' Qq'] (I : LocId Lc (D.what₂.places.resChar w) nV W' Qq')
    (B : GL (Fin D.R.k) D.host.E) (hB : Cmp.StdB D B) (𝔞 : Ideal (𝓞 D.host.E))
    (hL : Lc.Lb ⊔ 𝔞 • Submodule.span (𝓞 D.host.E) (dualSet (D.sp.cm.sig : D.host.E →+* D.host.E) D.sp.gram0 Lc.Lb) =
      D.sp.crdLat0 (D.sp.X 0).L0) : LocId Lc (D.what₂.places.resChar w) nV W' Qq' :=
  I.withFr B (fun x hx => (stdB_mem D B hB x).1 (hL ▸ (le_sup_left : Lc.Lb ≤ _) hx)) (D.mem u).A.T
    (fun w' hw' => natCast_notMem w' hg.1 hw' hg.2.2.2.2.2)
    (fun i => T_smul_mem Lc _ (companion_le Lc 𝔞 (hL ▸ (stdB_mem D B hB _).2 fun a => by
      rw [Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec]
      by_cases h : a = i
      · subst h
        exact ⟨1, by simp⟩
      · exact ⟨0, by simp [h]⟩)))

theorem locIdStd_fr (D : D7) (u : D.what₂.Word) (w : D.what₂.places.Pl) (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w))
    {Lc : ColLevel D.R D.host.F D.host.E D.sp D.host.g (D.mem u).C (D.mem u).A (D.clsLat u)} {nV : ℕ} {W' Qq' : Type}
    [CommRing W'] [Field Qq'] [Algebra W' Qq'] (I : LocId Lc (D.what₂.places.resChar w) nV W' Qq')
    (B : GL (Fin D.R.k) D.host.E) (hB : Cmp.StdB D B) (𝔞 : Ideal (𝓞 D.host.E))
    (hL : Lc.Lb ⊔ 𝔞 • Submodule.span (𝓞 D.host.E) (dualSet (D.sp.cm.sig : D.host.E →+* D.host.E) D.sp.gram0 Lc.Lb) =
      D.sp.crdLat0 (D.sp.X 0).L0)
    (w' : HeightOneSpectrum (𝓞 D.host.F)) (h : ((D.what₂.places.resChar w : ℕ) : 𝓞 D.host.F) ∈ w'.asIdeal) :
    (locIdStd D u w hg I B hB 𝔞 hL).fr w' h =
      bc (((RingHom.fst _ _).comp ((locIdStd D u w hg I B hB 𝔞 hL).spl w' h).toRingHom).comp
        (inclE (F := D.host.F) (w'.adicCompletion D.host.F))) B := rfl

theorem locIdStd_iw (D : D7) (u : D.what₂.Word) (w : D.what₂.places.Pl) (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w))
    {Lc : ColLevel D.R D.host.F D.host.E D.sp D.host.g (D.mem u).C (D.mem u).A (D.clsLat u)} {nV : ℕ} {W' Qq' : Type}
    [CommRing W'] [Field Qq'] [Algebra W' Qq'] (I : LocId Lc (D.what₂.places.resChar w) nV W' Qq')
    (B : GL (Fin D.R.k) D.host.E) (hB : Cmp.StdB D B) (𝔞 : Ideal (𝓞 D.host.E))
    (hL : Lc.Lb ⊔ 𝔞 • Submodule.span (𝓞 D.host.E) (dualSet (D.sp.cm.sig : D.host.E →+* D.host.E) D.sp.gram0 Lc.Lb) =
      D.sp.crdLat0 (D.sp.X 0).L0) : (locIdStd D u w hg I B hB 𝔞 hL).iw = I.iw := rfl

theorem companion_of_baseTied (D : D7) (H : Formalism.L2.Herm.HermCols D) (aT : ∀ u, Formalism.L2.Herm.AtT D u (H.vT u) (H.Fv u))
    (hb : Formalism.L2.Herm.BaseTied D H aT) (u : D.what₂.Word) :
    ∃ 𝔞 : Ideal (𝓞 D.host.E), (H.lev0 u).Lb ⊔ 𝔞 • Submodule.span (𝓞 D.host.E)
      (dualSet (D.sp.cm.sig : D.host.E →+* D.host.E) D.sp.gram0 (H.lev0 u).Lb) = D.sp.crdLat0 (D.sp.X 0).L0 := by
  have hi : IsIntegral ℤ (D.host.conj ((aT u).piU : D.host.E)) :=
    map_isIntegral_int D.host.conj (RingOfIntegers.isIntegral_coe _)
  exact ⟨Ideal.span {(⟨_, hi⟩ : 𝓞 D.host.E)}, (hb u ⟨_, hi⟩ rfl).1⟩

end Formalism.L2.G
