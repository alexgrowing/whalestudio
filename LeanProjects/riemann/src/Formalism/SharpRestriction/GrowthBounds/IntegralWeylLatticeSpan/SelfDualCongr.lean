import Formalism.SharpRestriction.GrowthBounds.IntegralWeylLatticeSpan.GramInvIntV
import Formalism.SharpRestriction.GrowthBounds.IntegralWeylLatticeSpan.RestGramW
import Formalism.LocalToGlobal.GlobalTheory.GL6.PBwLcInt
import Formalism.LocalToGlobal.GlobalTheory.GL6.PBwLocGlob
import Formalism.LocalToGlobal.GroupLattices.TiedFamilies.TiePtOneRec

noncomputable section

namespace Formalism.L2.G.RelativeIndexFlags

open Formalism.BasicNotions Formalism.MainNotions.G Formalism.L2.Forms NumberField IsDedekindDomain Matrix Formalism.UG Formalism.L2.G.Cmp
open scoped TensorProduct

section Gen

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}
  {σ : E →ₐ[F] E} {J : Matrix (Fin n) (Fin n) E} {T f : ℕ} {bad : Set (HeightOneSpectrum (𝓞 F))}

theorem selfDual_congr (v : HeightOneSpectrum (𝓞 F)) {L L' : Submodule (𝓞 E) (Fin n → E)}
    (h : latS (F := F) (v.adicCompletion F) (intV E v) L = latS (F := F) (v.adicCompletion F) (intV E v) L')
    (hs : SelfDualAt σ J v L) : SelfDualAt σ J v L' := by
  intro y
  have h1 : ∀ z, z ∈ latS (F := F) (v.adicCompletion F) (intV E v) L' ↔
      z ∈ latS (F := F) (v.adicCompletion F) (intV E v) L := fun z => by rw [h]
  exact (h1 y).trans ((hs y).trans ⟨fun H z hz => H z ((h1 z).1 hz), fun H z hz => H z ((h1 z).2 hz)⟩)

theorem loc_facts (S : StepLevel F E σ J T f bad) (v : HeightOneSpectrum (𝓞 F)) {p : ℕ} (hp : p.Prime)
    (hv : (p : 𝓞 F) ∈ v.asIdeal) (hT : ¬ p ∣ T) (Lc : Submodule (𝓞 E) (Fin n → E))
    (y : UPts σ J (FiniteAdeleRing (𝓞 F) F))
    (hy : ∀ x, x ∈ Formalism.L2.GlobalTheoryTheory.Comp.hat F Lc ↔
      ((y.1⁻¹ : GL (Fin n) _) : Matrix (Fin n) (Fin n) _) *ᵥ x ∈ Formalism.L2.GlobalTheoryTheory.Comp.hat F S.Lb)
    (hle : ∀ x ∈ Lc, x ∈ dualSet (σ : E →+* E) J Lc)
    (B' : GL (Fin n) E) (hB' : IsLocBasis p (dualSet (σ : E →+* E) J Lc) B') :
    SelfDualAt σ J v (latB B') ∧ ∀ (κ : S.U) (x : Fin n → E ⊗[F] v.adicCompletion F),
      x ∈ latS (F := F) (v.adicCompletion F) (intV E v) (latB B') ↔
        (((bc (prV (E := E) v) (y.1 * κ.1))⁻¹ : GL (Fin n) (E ⊗[F] v.adicCompletion F)) :
          Matrix (Fin n) (Fin n) (E ⊗[F] v.adicCompletion F)) *ᵥ x ∈ latS (F := F) (v.adicCompletion F) (intV E v) S.Lb := by
  have hsdb : SelfDualAt σ J v S.Lb := self_dual_lattice_at F E n σ J v S.Lb T S.Lb_fin
    (fun x hx y hy => S.Lb_int y hy x hx) (fun y hy => S.Lb_dual y hy) (natCast_notMem v hp hv hT)
  have hyl : ∀ x, x ∈ latS (F := F) (v.adicCompletion F) (intV E v) Lc ↔
      (((bc (prV (E := E) v) y.1)⁻¹ : GL (Fin n) (E ⊗[F] v.adicCompletion F)) :
        Matrix (Fin n) (Fin n) (E ⊗[F] v.adicCompletion F)) *ᵥ x ∈ latS (F := F) (v.adicCompletion F) (intV E v) S.Lb := by
    intro x
    rw [← map_inv]
    exact Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.rlv_yloc v y.1 hy x
  have hsdc : SelfDualAt σ J v Lc := selfDual_move v (bc (prV (E := E) v) y.1) (Formalism.UG.P.afsplit_bc_mem σ J v _ y.2) hyl hsdb
  have hLd : ((dualL (σ : E →+* E) J Lc : Submodule (𝓞 E) (Fin n → E)) : Set (Fin n → E)) = dualSet (σ : E →+* E) J Lc :=
    Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.bwG_span_dualSet _ _ _
  have e1 := latS_dual_eq v hLd (fun x hx => Submodule.subset_span (hle x hx)) hsdc
  have e2 := latS_of_locBasis v hp hv (dualL (σ : E →+* E) J Lc) B' (by rw [hLd]; exact hB')
  have e : latS (F := F) (v.adicCompletion F) (intV E v) Lc = latS (F := F) (v.adicCompletion F) (intV E v) (latB B') :=
    e1.symm.trans e2
  refine ⟨selfDual_congr v e hsdc, fun κ x => ?_⟩
  have hκ : bc (prV (E := E) v) κ.1 ∈ stabGL (latS (F := F) (v.adicCompletion F) (intV E v) S.Lb) :=
    (S.Uloc_lev v (((S.U_eq κ.1).1 κ.2).2 v)).2
  have hκ' := (stabGL (latS (F := F) (v.adicCompletion F) (intV E v) S.Lb)).inv_mem hκ
  rw [← e, hyl x, map_mul, _root_.mul_inv_rev, Units.val_mul, ← Matrix.mulVec_mulVec]
  exact hκ' _

variable {p : ℕ} {G : GAtP p}

theorem latW_gen (S : StepLevel F E σ J T f bad) (A : LocAt F E n G) (hW : LocInt A) (hp : p.Prime) (hT : ¬ p ∣ T)
    (halg : ∀ v (a : (A.pl v).1.adicCompletion F), A.spl v ((1 : E) ⊗ₜ[F] a) = (a, a))
    (hb : ∀ v (t : Fin n → (A.pl v).1.adicCompletion F),
      (∃ x ∈ Formalism.L2.Herm.locL (A.pl v).1 S.Lb, ∀ a, (A.spl v (x a)).1 = t a) ↔
      ∀ a, (((bc (A.phE v) A.B)⁻¹ : GL (Fin n) ((A.pl v).1.adicCompletion F)) :
        Matrix (Fin n) (Fin n) ((A.pl v).1.adicCompletion F)).mulVec t a ∈ (A.pl v).1.adicCompletionIntegers F)
    (Lc : Submodule (𝓞 E) (Fin n → E)) (y : UPts σ J (FiniteAdeleRing (𝓞 F) F))
    (hy : ∀ x, x ∈ Formalism.L2.GlobalTheoryTheory.Comp.hat F Lc ↔
      ((y.1⁻¹ : GL (Fin n) _) : Matrix (Fin n) (Fin n) _) *ᵥ x ∈ Formalism.L2.GlobalTheoryTheory.Comp.hat F S.Lb)
    (hle : ∀ x ∈ Lc, x ∈ dualSet (σ : E →+* E) J Lc)
    (B' : GL (Fin n) E) (hB' : IsLocBasis p (dualSet (σ : E →+* E) J Lc) B')
    (i : G.comp) (g : ∀ v, GL (Fin (G.P.m + 1)) (G.P.Qq v)) (γ : GL (Fin n) E) (κ : S.U)
    (hpt : A.IsPt i g (bc (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) γ * y.1 * κ.1)) (v : Fin G.P.nV) :
    colSpan (G.P.W v) (g v : Matrix (Fin (G.P.m + 1)) (Fin (G.P.m + 1)) (G.P.Qq v)) =
      colSpan (G.P.W v) (((castGL A.rk (G.P.Qq v)).symm (bc (A.iw v) (A.B⁻¹ * γ * B')) : GL (Fin (G.P.m + 1)) (G.P.Qq v)) :
        Matrix (Fin (G.P.m + 1)) (Fin (G.P.m + 1)) (G.P.Qq v)) := by
  obtain ⟨h1, h2⟩ := int_of_move (A.pl v).1 (A.spl v) (halg v) A.B B' (hb v) (bc (prV (E := E) (A.pl v).1) (y.1 * κ.1))
    ((loc_facts S (A.pl v).1 hp (A.pl v).2 hT Lc y hy hle B' hB').2 κ)
  exact lat_of_int A hW i g γ B' (y.1 * κ.1) (by rw [← mul_assoc]; exact hpt) v h1 h2

theorem gramW_gen (S : StepLevel F E σ J T f bad) (A : LocAt F E n G) (hW : LocInt A) (hp : p.Prime) (hT : ¬ p ∣ T)
    (halg : ∀ v (a : (A.pl v).1.adicCompletion F), A.spl v ((1 : E) ⊗ₜ[F] a) = (a, a)) (hJ : IsUnit J.det)
    (Lc : Submodule (𝓞 E) (Fin n → E)) (y : UPts σ J (FiniteAdeleRing (𝓞 F) F))
    (hy : ∀ x, x ∈ Formalism.L2.GlobalTheoryTheory.Comp.hat F Lc ↔
      ((y.1⁻¹ : GL (Fin n) _) : Matrix (Fin n) (Fin n) _) *ᵥ x ∈ Formalism.L2.GlobalTheoryTheory.Comp.hat F S.Lb)
    (hle : ∀ x ∈ Lc, x ∈ dualSet (σ : E →+* E) J Lc)
    (B' : GL (Fin n) E) (hB' : IsLocBasis p (dualSet (σ : E →+* E) J Lc) B') (v : Fin G.P.nV) (a b : Fin n) :
    A.iw v ((cT (σ : E →+* E) B'.1 * J * B'.1) a b) ∈ Set.range (algebraMap (G.P.W v) (G.P.Qq v)) ∧
      A.iw v ((cT (σ : E →+* E) B'.1 * J * B'.1)⁻¹ a b) ∈ Set.range (algebraMap (G.P.W v) (G.P.Qq v)) := by
  have hsd := (loc_facts S (A.pl v).1 hp (A.pl v).2 hT Lc y hy hle B' hB').1
  have hG : IsUnit (cT (σ : E →+* E) (B' : Matrix (Fin n) (Fin n) E) * J * (B' : Matrix (Fin n) (Fin n) E)).det := by
    rw [Matrix.det_mul, Matrix.det_mul]
    refine (IsUnit.mul ?_ hJ).mul ((Matrix.isUnit_iff_isUnit_det _).1 B'.isUnit)
    have h0 := (Matrix.isUnit_iff_isUnit_det _).1 (bc (σ : E →+* E) B').isUnit
    show IsUnit (((bc (σ : E →+* E) B' : GL (Fin n) E) : Matrix (Fin n) (Fin n) E)ᵀ).det
    rw [Matrix.det_transpose]
    exact h0
  have key : ∀ x : E, inclE (F := F) ((A.pl v).1.adicCompletion F) x ∈ intV E (A.pl v).1 →
      A.iw v x ∈ Set.range (algebraMap (G.P.W v) (G.P.Qq v)) := by
    intro x hx
    refine (hW v _).2 ?_
    have e : A.eQ v (A.iw v x) = (A.spl v (inclE (F := F) ((A.pl v).1.adicCompletion F) x)).1 :=
      (A.eQ v).apply_symm_apply _
    rw [e]
    exact Formalism.MainNotions.Gaps.Loc.fst_int (A.pl v).1 (A.spl v) (halg v) _ hx
  exact ⟨key _ (gram_intV (A.pl v).1 B' hsd a b), key _ (gramInv_intV (A.pl v).1 B' hsd hG a b)⟩

theorem frlat_re {k : ℕ} (hk : k = n) (v : HeightOneSpectrum (𝓞 F))
    (φ : E ⊗[F] v.adicCompletion F ≃+* v.adicCompletion F × v.adicCompletion F)
    (Lb0 : Submodule (𝓞 E) (Fin k → E)) (B0 : GL (Fin k) E) (fr : GL (Fin k) (v.adicCompletion F))
    (hfr : fr = bc (piE v φ) B0)
    (h : ∀ t : Fin k → v.adicCompletion F, (∃ x ∈ Formalism.L2.Herm.locL v Lb0, ∀ a, (φ (x a)).1 = t a) ↔
      ∀ a, ((fr⁻¹ : GL (Fin k) (v.adicCompletion F)) :
        Matrix (Fin k) (Fin k) (v.adicCompletion F)).mulVec t a ∈ v.adicCompletionIntegers F)
    (Lb' : Submodule (𝓞 E) (Fin n → E)) (hLb : Lb' = reL hk Lb0) :
    ∀ t : Fin n → v.adicCompletion F, (∃ x ∈ Formalism.L2.Herm.locL v Lb', ∀ a, (φ (x a)).1 = t a) ↔
      ∀ a, (((bc (piE v φ) (reGL hk E B0))⁻¹ : GL (Fin n) (v.adicCompletion F)) :
        Matrix (Fin n) (Fin n) (v.adicCompletion F)).mulVec t a ∈ v.adicCompletionIntegers F := by
  subst hk
  subst hfr
  subst hLb
  have e1 : reL (rfl : k = k) Lb0 = Lb0 := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩; exact hy
    · intro hx; exact ⟨x, hx, rfl⟩
  rw [e1, reGL_rfl]
  exact h

end Gen

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {X : Formalism.L2.Herm.Herm0 D}

set_option maxHeartbeats 4000000 in

theorem hb_rec (T : ∀ u : D.what₂.Word, Forms0 D u) (I : CmpIn D X) (hJ : ∀ u, Joint0 X.lev0 u (T u)) (u : D.what₂.Word)
    (w : D.what₂.places.Pl) (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)) (v : Fin (D.gat u w hg).P.nV)
    (t : Fin (D.R.N 0) → ((locAt X u w hg I.B).pl v).1.adicCompletion D.host.F) :
    (∃ x ∈ Formalism.L2.Herm.locL ((locAt X u w hg I.B).pl v).1 ((T u).cls0).lev.Lb,
        ∀ a, ((locAt X u w hg I.B).spl v (x a)).1 = t a) ↔
      ∀ a, (((bc ((locAt X u w hg I.B).phE v) (locAt X u w hg I.B).B)⁻¹ :
        GL (Fin (D.R.N 0)) (((locAt X u w hg I.B).pl v).1.adicCompletion D.host.F)) :
        Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) _).mulVec t a ∈
          ((locAt X u w hg I.B).pl v).1.adicCompletionIntegers D.host.F := by
  exact frlat_re (rank_eq_first_level D.R) ((X.g u w hg).pl v).1 ((X.g u w hg).spl _ ((X.g u w hg).pl v).2) (X.lev0 u).Lb I.B
    ((X.g u w hg).fr _ ((X.g u w hg).pl v).2) (I.fr_B u w hg _ ((X.g u w hg).pl v).2)
    ((X.g u w hg).fr_lat _ ((X.g u w hg).pl v).2) ((T u).cls0).lev.Lb (hJ u).Lb_eq t

set_option maxHeartbeats 1000000 in
set_option synthInstance.maxHeartbeats 400000 in

theorem lcInt_of_cls {u : D.what₂.Word} {i : ℕ} {hi : i ≤ D.R.m} (K : ClsTied u i hi) (c : (D.mem u).C.cls i) :
    clsCrd D u i hi c ≤ Ld D u i hi c := by
  intro x hx
  apply Submodule.subset_span
  intro x' hx'
  have hglob : ∀ z ∈ clsCrd D u i hi c, z ∈ Formalism.UG.CS.globLat (K.y c).1 K.lev.Lb := by
    intro z hz
    exact (K.y_lat c _).1 (Submodule.subset_span ⟨z, hz, rfl⟩)
  have hm : ∀ a ∈ K.lev.Lb, ∀ b ∈ K.lev.Lb,
      IsIntegral ℤ (((1 : ℤ) : D.host.E) * Formalism.UG.hform (sigD D : D.host.E →+* D.host.E) (gramN D i hi) a b) := by
    intro a ha b hb
    obtain ⟨r, hr⟩ := K.lev.Lb_int b hb a ha
    rw [Int.cast_one, one_mul, ← hr]
    exact RingOfIntegers.isIntegral_coe r
  have h := Formalism.UG.P.csScale_glob (sigD D) (gramN D i hi) K.lev.Lb 1 hm (K.y c).1
    (K.y c).2 (hglob x' hx') (hglob x hx)
  rw [Int.cast_one, one_mul] at h
  exact Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.bwL_descent _ _ _ h

set_option maxHeartbeats 4000000 in
theorem hle_rec (T : ∀ u : D.what₂.Word, Forms0 D u) (u : D.what₂.Word) (c : (D.mem u).C.cls 0) :
    ∀ x ∈ clsCrd D u 0 (Nat.zero_le _) c,
      x ∈ dualSet (sigD D : D.host.E →+* D.host.E) (gramN D 0 (Nat.zero_le _)) (clsCrd D u 0 (Nat.zero_le _) c) := by
  intro x hx
  have h := lcInt_of_cls (T u).cls0 c hx
  rw [← SetLike.mem_coe, Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.bwG_Ld_coe] at h
  exact h

set_option maxHeartbeats 8000000 in

theorem restLatW_of (T : ∀ u : D.what₂.Word, Forms0 D u) (I : CmpIn D X) (hJ : ∀ u, Joint0 X.lev0 u (T u)) :
    RestLatW T I := by
  intro u w hg i L c g γ κ hL _ hpt B' hB' v
  rw [hL v]
  exact latW_gen ((T u).cls0).lev (locAt X u w hg I.B) (locInt_locAt X u w hg I.B) hg.1 hg.2.2.2.2.2
    (fun v a => (X.g u w hg).spl_alg _ ((X.g u w hg).pl v).2 a) (hb_rec T I hJ u w hg)
    (clsCrd D u 0 (Nat.zero_le _) c) (((T u).cls0).y c) (((T u).cls0).y_lat c)
    (hle_rec T u c) B' hB' i g γ κ hpt v

set_option maxHeartbeats 8000000 in

theorem restGramW_of (T : ∀ u : D.what₂.Word, Forms0 D u) (I : CmpIn D X) : RestGramW I := by
  intro u w hg c B' hB' v a b
  exact gramW_gen ((T u).cls0).lev (locAt X u w hg I.B) (locInt_locAt X u w hg I.B) hg.1 hg.2.2.2.2.2
    (fun v a => (X.g u w hg).spl_alg _ ((X.g u w hg).pl v).2 a) (Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.bwB_gramN_det D 0 (Nat.zero_le _))
    (clsCrd D u 0 (Nat.zero_le _) c) (((T u).cls0).y c) (((T u).cls0).y_lat c)
    (hle_rec T u c) B' hB' v a b

end Formalism.L2.G.RelativeIndexFlags
