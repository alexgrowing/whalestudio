import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.TieEmbeddingCastLevelTie
import Formalism.LocalToGlobal.GroupLattices.TiedFamilies.TieAll
import Formalism.LocalToGlobal.GroupLattices.TiedFamilies.TieFin
import Formalism.LocalToGlobal.GroupLattices.TiedFamilies.GTiedFOfIsRecCEv
import Formalism.LocalToGlobal.GroupLattices.TiedFamilies.TiePsiC
import Formalism.LocalToGlobal.GroupLattices.TiedFamilies.BlockRationalityField
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.BlockRatReal
import Formalism.SharpRestriction.GrowthBounds.IntegralWeylLatticeSpan.WeylLatticeDescentHolds
import Formalism.SharpRestriction.GrowthBounds.IntegralWeylLatticeSpan.ColSpanMulUnit
import Formalism.SharpRestriction.GrowthBounds.IntegralWeylLatticeSpan.SelfDualCongr
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CharZeroOfSetting
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLocIdOfCompletions
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AddCharIsIntegral

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.L2.G NumberField IsDedekindDomain Formalism.UG Formalism.L2.Forms

namespace GlobalTheory.Mem.LocalPack.Test

attribute [local instance] Formalism.BasicNotions.factResChar Formalism.BasicNotions.Host.cmStar

theorem exists_place_over (F : Type) [Field F] [NumberField F] {p : ℕ} (hp : p.Prime) :
    ∃ v : HeightOneSpectrum (𝓞 F), (p : 𝓞 F) ∈ v.asIdeal := by
  have hp0 : (p : 𝓞 F) ≠ 0 := by exact_mod_cast hp.ne_zero
  have hnu : ¬ IsUnit (p : 𝓞 F) := by
    intro h
    have h1 : IsUnit (Algebra.norm ℤ (p : 𝓞 F)) := h.map _
    have h2 : Algebra.norm ℤ (p : 𝓞 F) = (p : ℤ) ^ Module.finrank ℤ (𝓞 F) := by
      have := Algebra.norm_algebraMap (R := ℤ) (S := 𝓞 F) (p : ℤ)
      simpa using this
    rw [h2, isUnit_pow_iff Module.finrank_pos.ne', Int.isUnit_iff_natAbs_eq] at h1
    exact hp.ne_one (by simpa using h1)
  obtain ⟨M, hM, hle⟩ := Ideal.exists_le_maximal (Ideal.span {(p : 𝓞 F)}) (by rwa [Ne, Ideal.span_singleton_eq_top])
  have hmem : (p : 𝓞 F) ∈ M := hle (Ideal.mem_span_singleton_self _)
  exact ⟨⟨M, hM.isPrime, fun h => hp0 (by simpa [h] using hmem)⟩, hmem⟩

theorem orbits_pos {D : D7} {H : LevelData D} {u : D.what₂.Word} {w : D.what₂.places.Pl}
    {hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)} (h : LocalIs D H u w hg) : 0 < (D.gat u w hg).P.nV := by
  obtain ⟨W, Qq, O, Kf, _, _, _, _, _, _, _, _, _, _, n', ι, σ, j, w0, hS, nV, r, m, lam0, dom, hk, I, ψ, e, hH, heq⟩ := h
  rw [heq]
  obtain ⟨v, hv⟩ := exists_place_over D.host.F hg.1
  exact (I.pl.symm ⟨v, hv⟩).pos

theorem rank_eq {D : D7} {H : LevelData D} {u : D.what₂.Word} {w : D.what₂.places.Pl}
    {hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)} (h : LocalIs D H u w hg) :
    (D.gat u w hg).P.m + 1 = D.R.k := by
  obtain ⟨W, Qq, O, Kf, _, _, _, _, _, _, _, _, _, _, n', ι, σ, j, w0, hS, nV, r, m, lam0, dom, hk, I, ψ, e, hH, heq⟩ := h
  rw [heq]
  exact hk

theorem finClasses_and_trivStab {D : D7} {H : LevelData D} {u : D.what₂.Word} {w : D.what₂.places.Pl}
    {hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)} (h : LocalIs D H u w hg) :
    (D.gat u w hg).FinClasses ∧ (Cmp.TrivStabU (H u) → (D.gat u w hg).TrivStab) := by
  obtain ⟨W, Qq, O, Kf, _, _, _, _, _, _, _, _, _, _, n', ι, σ, j, w0, hS, nV, r, m, lam0, dom, hk, I, ψ, e, hH, heq⟩ := h
  rw [heq]
  exact ⟨Cmp.finClasses hS r lam0 dom hk I ψ e (isUnit_det_gram0 D.sp) hH,
    fun hT => Cmp.trivStab hS r lam0 dom hk I ψ e (isUnit_det_gram0 D.sp) hH hT⟩

theorem orbit_length {D : D7} {Gt : GatTies D} {c : LatCmp D} (h : IsConcrete D Gt c) (u : D.what₂.Word)
    (w : D.what₂.places.Pl) (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)) (v : Fin (D.gat u w hg).P.nV) :
    (D.gat u w hg).P.n' v = frobOrder D (D.what₂.places.resChar w) := by
  obtain ⟨D0, sc, Lc, I, ψ, hd, H0, hL, T, B, hBs, hB, iK, lam, hK, hPos, CH, heq⟩ := h
  cases heq
  rfl

set_option maxHeartbeats 4000000 in

theorem coefficient_ring {D : D7} {Gt : GatTies D} {c : LatCmp D} (h : IsConcrete D Gt c) (u : D.what₂.Word)
    (w : D.what₂.places.Pl) (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)) :
    (D.gat u w hg).O = ORec D w (frobOrder D (D.what₂.places.resChar w)) := by
  obtain ⟨D0, sc, Lc, I, ψ, hd, H0, hL, T, B, hBs, hB, iK, lam, hK, hPos, CH, heq⟩ := h
  cases heq
  rfl

theorem exists_embedding_of_ringTie {D : D7} {u : D.what₂.Word} {w : D.what₂.places.Pl}
    {hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)} {v : Fin (D.gat u w hg).P.nV} (h : RingTie D u w hg v) :
    ∃ e : D.what₂.LL →+* (D.gat u w hg).Kf, ∀ x, (0 : WithTop ℤ) ≤ D.what₂.places.val w x ↔
      e x ∈ Set.range (algebraMap (D.gat u w hg).O (D.gat u w hg).Kf) := by
  obtain ⟨eW, eQ, eO, eK, -, hOK, -, -, -⟩ := h
  refine ⟨eK.toRingHom.comp (embRec D w _), fun x => (embRec_int D w ((D.gat u w hg).P.n' v) x).trans ⟨?_, ?_⟩⟩
  · rintro ⟨y, hy⟩
    exact ⟨eO y, by rw [← hOK, hy]; rfl⟩
  · rintro ⟨y, hy⟩
    refine ⟨eO.symm y, eK.injective ?_⟩
    rw [hOK, RingEquiv.apply_symm_apply, hy]
    rfl

theorem localIs_record_free (D : D7) (sc : Scale) (Ce : ℝ)
    (Lc : ∀ u, ColLevel D.R D.host.F D.host.E D.sp D.host.g (D.mem u).C (D.mem u).A (D.clsLat u))
    (I) (ψ) (hd) (u : D.what₂.Word) (w : D.what₂.places.Pl) (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)) :
    LocalIs (record D sc Ce Lc I ψ hd) Lc u w hg :=
  localIs_of_hyperspecial D sc Ce Lc (packAll D Lc I ψ) hd Lc (fun _ => rfl)
    (fun u w h => isHyperbolicAt_rec_of_placeIdentification D u w h (I u w h)) u w hg

theorem exists_hermTies (D : D7) (sc : Scale) (Ce : ℝ)
    (Lc : ∀ u, ColLevel D.R D.host.F D.host.E D.sp D.host.g (D.mem u).C (D.mem u).A (D.clsLat u))
    (I) (ψ) (hd) : ∃ H0 : Formalism.L2.Herm.Herm0 (record D sc Ce Lc I ψ hd), ∀ u, H0.lev0 u = Lc u :=
  ⟨⟨Lc, levTieG D sc Ce Lc (packAll D Lc I ψ) hd⟩, fun _ => rfl⟩

theorem forms_and_basis {D : D7} {Gt : GatTies D} {c : LatCmp D} (h : IsConcrete D Gt c) :
    (∀ u, Nonempty (Forms0 D u)) ∧ ∃ B, Cmp.StdB D B :=
  h.nonempty_allTies.elim fun G => ⟨fun u => ⟨G.forms u⟩, G.cmp.B, G.cmp.B_std⟩

theorem exponent_eq {D : D7} {Gt : GatTies D} {c : LatCmp D} (h : IsConcrete D Gt c) :
    ∃ sc : Scale, ∀ u w hg, (D.gat u w hg).e = epSc D.R sc 1 (D.what₂.places.resChar w) ∧
      (D.gat u w hg).P.r = rSc sc D.R.k (D.what₂.places.resChar w) := by
  obtain ⟨D0, sc, Lc, I, ψ, hd, H0, hL, T, B, hBs, hB, iK, lam, hK, hPos, CH, heq⟩ := h
  cases heq
  exact ⟨sc, fun _ _ _ => ⟨rfl, rfl⟩⟩

section Reduction

open Formalism.L2.G.Cmp Formalism.L2.G.RelativeIndexFlags

theorem block_rational : Formalism.L2.G.BlockRationalityField := by
  intro p O Kf _ _ _ _ _ P Tau _ n LL _ h pos G M embLL lam hW hM
  exact blockRatReal P.lam0 h pos G M embLL (fun τ => (lam τ).w) (fun τ => (lam τ).anti) hW hM

variable (D : D7) (sc : Scale)
  (Lc : ∀ u, ColLevel D.R D.host.F D.host.E D.sp D.host.g (D.mem u).C (D.mem u).A (D.clsLat u))
  (I : ∀ u (w : D.what₂.places.Pl), GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w) →
    LocId (Lc u) (D.what₂.places.resChar w) (nOrb (zH D.R.toFrame (hP D (D.what₂.places.resChar w))))
      (WQ (D.what₂.places.resChar w) (nFr D (D.what₂.places.resChar w)))
      (QQ (D.what₂.places.resChar w) (nFr D (D.what₂.places.resChar w))))
  (ψ : ∀ u (w : D.what₂.places.Pl), GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w) →
    Formalism.L2.Herm.awayFrom₂ (Lc u) (D.what₂.places.resChar w) →* (ORec D w (nFr D (D.what₂.places.resChar w)))ˣ)
  (hd : ∀ u w h, ((packC D Lc I ψ u w h).gat (rSc sc D.R.k (D.what₂.places.resChar w))
    (epSc D.R sc 1 (D.what₂.places.resChar w))).d = Module.finrank ℂ (D.mem u).A.Mu0)
  (H0 : Formalism.L2.Herm.Herm0 (recC D sc 1 Lc I ψ hd)) (hL : ∀ u, H0.lev0 u = Lc u)
  (T : ∀ u : D.what₂.Word, Forms0 (recC D sc 1 Lc I ψ hd) u)
  (B : GL (Fin D.R.k) D.host.E) (hBs : Cmp.StdB (recC D sc 1 Lc I ψ hd) B)
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

set_option maxHeartbeats 32000000 in
include hK hPos in

theorem comparison_statements (hJ : ∀ u, Joint0 H0.lev0 u (T u))
    (h0 : ∀ u, LevelZeroCharacterRational (D := recC D sc 1 Lc I ψ hd) T u)
    (hψ : ∀ u (w : D.what₂.places.Pl) (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)),
      PsiTied (LL := D.what₂.LL) (O := ORec D w (nFr D (D.what₂.places.resChar w)))
        (Kf := KfRec D w (nFr D (D.what₂.places.resChar w)))
        ((T u).cls0).lev (Lc u) (D.what₂.places.resChar w) (rank_eq_first_level D.R) D.what₂.embLL
        ((cmpInC D sc 1 Lc I ψ hd H0 hL B hBs hB).embW u w hg) (ψ u w hg)) :
    CmpHyp0P T (gatTiesC D sc 1 Lc I ψ hd) (cmpInC D sc 1 Lc I ψ hd H0 hL B hBs hB) := by
  have hpos := fun u w hg v s x => pos_C D sc 1 Lc I ψ hd H0 hL B hBs hB iK lam hK hPos u w hg v s x
  have hs : ∀ u, SameUloc (hermitianLevelZeroOfRecursion D sc 1 Lc I ψ hd H0 hL) T u :=
    fun u => sameUloc_of_joint (hermitianLevelZeroOfRecursion D sc 1 Lc I ψ hd H0 hL) T u (hJ u)
  have N : CmpLeft D sc 1 Lc I ψ hd H0 hL T B hBs hB :=
    { same := hs
      blk := fun u w hg => blkRatRec_of_stmt block_rational _ _ u w hg B
      psi0 := h0
      chi := chi_C D sc 1 Lc I ψ hd H0 hL T B hBs hB hψ
      valInt := valIntRec_of weylLatticeDescent_holds
        (fun u w hg => ex_C_blk D sc 1 Lc I ψ hd H0 hL T B hBs hB u (hs u) w hg
          (blkRatRec_of_stmt block_rational _ _ u w hg B) (h0 u))
        (fun u w hg => frac_of_gatIs _ u w hg (gatIs_recC D sc 1 Lc I ψ hd H0 hL
          (fun u w h => isHyperbolicAt_rec_of_placeIdentification D u w h (I u w h)) u w hg))
        (restExB _)
        (restLatO_of hpos (restLatW_of (D := recC D sc 1 Lc I ψ hd) T (cmpInC D sc 1 Lc I ψ hd H0 hL B hBs hB) (fun u => hJ u))
          (restGramW_of (D := recC D sc 1 Lc I ψ hd) T (cmpInC D sc 1 Lc I ψ hd H0 hL B hBs hB)))
        (restChi_of (D := recC D sc 1 Lc I ψ hd) T h0) }
  exact N.toHyp0P hpos

set_option maxHeartbeats 32000000 in
include hBs hB hK hPos hL in

theorem exists_isConcrete (hJ : ∀ u, Joint0 H0.lev0 u (T u))
    (h0 : ∀ u, LevelZeroCharacterRational (D := recC D sc 1 Lc I ψ hd) T u)
    (hψ : ∀ u (w : D.what₂.places.Pl) (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)),
      PsiTied (LL := D.what₂.LL) (O := ORec D w (nFr D (D.what₂.places.resChar w)))
        (Kf := KfRec D w (nFr D (D.what₂.places.resChar w)))
        ((T u).cls0).lev (Lc u) (D.what₂.places.resChar w) (rank_eq_first_level D.R) D.what₂.embLL
        (embRec D w (nFr D (D.what₂.places.resChar w))) (ψ u w hg)) :
    ∃ c, IsConcrete (recC D sc 1 Lc I ψ hd) (gatTiesC D sc 1 Lc I ψ hd) c :=
  ⟨_, IsConcrete.intro D sc Lc I ψ hd H0 hL T B hBs hB iK lam hK hPos
    (comparison_statements D sc Lc I ψ hd H0 hL T B hBs hB iK lam hK hPos hJ h0 hψ) rfl⟩

end Reduction

theorem isConcrete_record_iff (D : D7) (sc : Scale) (Ce : ℝ)
    (Lc : ∀ u, ColLevel D.R D.host.F D.host.E D.sp D.host.g (D.mem u).C (D.mem u).A (D.clsLat u))
    (I) (ψ) (hd) (hd') :
    (∃ c, IsConcrete (record D sc Ce Lc I ψ hd') (recordTies D sc Ce Lc I ψ hd') c) ↔
      ∃ c, IsConcrete (recC D sc Ce Lc I ψ hd) (gatTiesC D sc Ce Lc I ψ hd) c := by
  have key : ∀ X X' (_ : X = X') h h', (∃ c, IsConcrete (recG D sc Ce Lc X h) (gatTiesG D sc Ce Lc X h) c) ↔
      ∃ c, IsConcrete (recG D sc Ce Lc X' h') (gatTiesG D sc Ce Lc X' h') c := by
    intro X X' e h h'
    subst e
    rfl
  exact key _ _ (packAll_eq D Lc I ψ) hd' hd

theorem baseLattice_standard {D : D7} {Gt : GatTies D} {c : LatCmp D} (G : AllTies D Gt c) :
    ∃ B : GL (Fin D.R.k) D.host.E, Cmp.StdB D B ∧
      ∀ u (w : D.what₂.places.Pl) (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w))
        (w' : HeightOneSpectrum (𝓞 D.host.F)) (h : ((D.what₂.places.resChar w : ℕ) : 𝓞 D.host.F) ∈ w'.asIdeal)
        (t : Fin D.R.k → w'.adicCompletion D.host.F),
        (∃ x ∈ Formalism.L2.Herm.locL w' (G.herm.lev0 u).Lb, ∀ a, ((G.herm.g u w hg).spl w' h (x a)).1 = t a) ↔
          ∀ a, (((bc (((RingHom.fst _ _).comp ((G.herm.g u w hg).spl w' h).toRingHom).comp
            (inclE (F := D.host.F) (w'.adicCompletion D.host.F))) B)⁻¹ : GL (Fin D.R.k) (w'.adicCompletion D.host.F)) :
              Matrix (Fin D.R.k) (Fin D.R.k) (w'.adicCompletion D.host.F)).mulVec t a ∈
                w'.adicCompletionIntegers D.host.F := by
  refine ⟨G.cmp.B, G.cmp.B_std, fun u w hg w' h t => ?_⟩
  rw [← G.cmp.fr_B u w hg w' h]
  exact (G.herm.g u w hg).fr_lat w' h t

theorem isConcrete_iff (D : D7) (Gt : GatTies D) (c : LatCmp D) : IsConcrete D Gt c ↔ IsRecC D Gt c := by
  constructor
  · rintro ⟨D0, sc, Lc, I, ψ, hd, H0, hL, T, B, hBs, hB, iK, lam, hK, hPos, CH, heq⟩
    exact ⟨D0, sc, Lc, I, ψ, hd, H0, hL, T, B, hBs, hB, iK, lam, hK, hPos, CH, heq⟩
  · rintro ⟨D0, sc, Lc, I, ψ, hd, H0, hL, T, B, hBs, hB, iK, lam, hK, hPos, CH, heq⟩
    exact ⟨D0, sc, Lc, I, ψ, hd, H0, hL, T, B, hBs, hB, iK, lam, hK, hPos, CH, heq⟩

set_option maxHeartbeats 32000000 in

theorem exists_concrete_of_record (D : D7) (L0 : LevelData D) (T : ∀ u : D.what₂.Word, Forms0 D u)
    (hS : Formalism.L2.Herm.StdTied D) (hJ : ∀ u, Joint0 L0 u (T u)) (h0 : ∀ u, LevelZeroCharacterRational T u)
    (hb : ∀ u, ∃ 𝔞 : Ideal (𝓞 D.host.E), (L0 u).Lb ⊔ 𝔞 • Submodule.span (𝓞 D.host.E)
      (dualSet (D.sp.cm.sig : D.host.E →+* D.host.E) D.sp.gram0 (L0 u).Lb) = D.sp.crdLat0 (D.sp.X 0).L0)
    (sc : Scale) : ∃ I ψ hd c, IsConcrete (recC D sc 1 L0 I ψ hd) (gatTiesC D sc 1 L0 I ψ hd) c := by
  obtain ⟨B, hB⟩ := exists_stdB_of_tied D hS
  choose 𝔞 h𝔞 using hb
  choose I0 iK lam hK hPos using fun u w hg => GlobalTheory.PlaceOrbit.exists_locId D u (L0 u) w hg
  choose ψ hψ using fun u w hg => GlobalTheory.Mem.AwayChar.exists_psi D L0 T hJ h0 u w hg
  let I := fun u w hg => locIdStd D u w hg (I0 u w hg) B hB (𝔞 u) (h𝔞 u)
  have hd : ∀ u w h, ((packC D L0 I ψ u w h).gat (rSc sc D.R.k (D.what₂.places.resChar w))
      (epSc D.R sc 1 (D.what₂.places.resChar w))).d = Module.finrank ℂ (D.mem u).A.Mu0 := by
    intro u w h
    exact GlobalTheory.ClassRank.pack_d_eq D L0 T hJ u w h _ _ _ _
  refine ⟨I, ψ, hd, ?_⟩
  refine exists_isConcrete D sc L0 I ψ hd ⟨L0, levTieG D sc 1 L0 (packC D L0 I ψ) hd⟩ (fun _ => rfl)
    (formsOfRecursion D sc 1 L0 I ψ hd T) B hB (fun _ _ _ _ _ => rfl) iK lam hK ?_ ?_ ?_ ?_
  · intro u w hg
    exact hPos u w hg (ψ u w hg)
  · exact fun u => hJ u
  · exact fun u => h0 u
  · exact fun u w hg => hψ u w hg

end GlobalTheory.Mem.LocalPack.Test
