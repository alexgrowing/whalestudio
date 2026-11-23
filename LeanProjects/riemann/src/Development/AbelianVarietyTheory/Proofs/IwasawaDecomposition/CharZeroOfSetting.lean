import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FrobOrderSpec
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EvalRepsSurjective
import Formalism.LocalToGlobal.GlobalTheory.CoordinateLengths.DuCount
import Formalism.LocalToGlobal.GroupLattices.ComparisonMaps.DeterminantTwistRowActionMem
import Formalism.LocalToGlobal.GroupLattices.ComparisonMaps.ClsRec
import Formalism.LocalToGlobal.GroupLattices.TiedFamilies.SelfDualAtColLevel
import Formalism.LocalToGlobal.GroupLattices.TrivialTransfer.GramTotallyDefinite
import Formalism.LocalToGlobal.GroupLattices.FockModels.WeylDim
import Formalism.LocalToGlobal.GroupLattices.FockModels.Cartan
import Formalism.LocalRingCardinality.SpanPowerMembership.NZLevB
import Formalism.SharpRestriction.GrowthBounds.ScaleEdges.WeylDimShift
import Formalism.SharpRestriction.GrowthBounds.DualFockLinear.TestSideCounting

open MvPolynomial Formalism.MainNotions.G Formalism.GradedWeylDivisibility Formalism.L2.G.Model

noncomputable section

namespace GlobalTheory.ClassRank

section General

theorem charZero_of_setting {p n' : ℕ} {W Qq O Kf : Type} [CommRing W] [IsDomain W] [IsDiscreteValuationRing W]
    [Field Qq] [Algebra W Qq] [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field Kf] [Algebra O Kf]
    {ι : Qq →+* Kf} {σ : Qq ≃+* Qq} {j : W →+* O} {w : O} (hS : HidaSetting p n' W Qq O Kf ι σ j w) : CharZero Kf := by
  have hW : CharZero W := by
    obtain ⟨l, hl⟩ := CharP.exists W
    rcases CharP.char_is_prime_or_zero W l with hp | rfl
    · exfalso
      by_cases h : l = p
      · subst h
        exact hS.p_unif.ne_zero (CharP.cast_eq_zero W l)
      · apply hS.p_unif.not_isUnit
        have hc : Nat.Coprime p l := (Nat.coprime_primes hS.prime hp).2 (Ne.symm h)
        have h1 := (Nat.isCoprime_iff_coprime.2 hc).map (Int.castRingHom W)
        simp only [eq_intCast, Int.cast_natCast, CharP.cast_eq_zero] at h1
        exact isCoprime_zero_right.1 h1
    · exact CharP.charP_to_charZero W
  have := hS.frac_alt
  have hQ : CharZero Qq := charZero_of_injective_algebraMap (IsFractionRing.injective W Qq)
  exact charZero_of_injective_ringHom ι.injective

theorem span_map_weyl (O : Type) [CommRing O] (k : ℕ) (ν : Fin k → ℕ) {ι : Type}
    (b : Module.Basis ι ℤ (weyl ℤ k k le_rfl ν)) :
    Submodule.span O (Set.range fun i => MvPolynomial.map (Int.castRingHom O) (b i : MvPolynomial (Fin k × Fin k) ℤ)) =
      weyl O k k le_rfl ν := by
  let f : weyl ℤ k k le_rfl ν →ₗ[ℤ] MvPolynomial (Fin k × Fin k) O :=
    (map (Int.castRingHom O) : MvPolynomial (Fin k × Fin k) ℤ →+* MvPolynomial (Fin k × Fin k) O).toIntAlgHom.toLinearMap.comp
      (Submodule.subtype _)
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    exact sw_weyl_map (Int.castRingHom O) le_rfl ν _ (b i).2
  · show Submodule.span O (Set.range fun w => applyWord O w (hw O (le_refl k) ν)) ≤ _
    rw [Submodule.span_le]
    rintro _ ⟨w, rfl⟩
    show applyWord O w (hw O (le_refl k) ν) ∈ _
    have hmem : applyWord ℤ w (hw ℤ (le_refl k) ν) ∈ weyl ℤ k k le_rfl ν := Submodule.subset_span ⟨w, rfl⟩
    have hsp : (⟨_, hmem⟩ : weyl ℤ k k le_rfl ν) ∈ Submodule.span ℤ (Set.range b) := by
      rw [b.span_eq]; trivial
    have h2 := Submodule.mem_map_of_mem (f := f) hsp
    rw [Submodule.map_span, ← Set.range_comp] at h2
    rw [← lclosedeq_hw_map (Int.castRingHom O) (le_refl k) ν, lclosedeq_applyWord_map]
    exact Submodule.span_le_restrictScalars ℤ O _ h2

theorem exists_basis_Dl0 {O Kf : Type} [CommRing O] [Field Kf] [Algebra O Kf] [CharZero Kf]
    (hinj : Function.Injective (algebraMap O Kf)) (m : ℕ) (lam : Fin (m + 1) → ℤ) (hlam : Antitone lam)
    (Λ : Submodule O (Fin (m + 1) → Kf)) (hΛ : IsLattice O Λ) :
    ∃ B : Fin (Nat.card (ssIdx (m + 1) (m + 1) (nuOf lam))) → MvPolynomial (Fin (m + 1) × Fin (m + 1)) Kf,
      LinearIndependent Kf B ∧ Submodule.span O (Set.range B) = Dl0 O m lam Λ := by
  obtain ⟨g, hg, rfl⟩ := hΛ
  have hν : Antitone (nuOf lam) := toNat_antitone lam hlam
  obtain ⟨ι, hι, b0, -⟩ := Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.weyl_homogeneous_basis (le_refl (m + 1)) (nuOf lam) hν
  have hcard : Fintype.card ι = Nat.card (ssIdx (m + 1) (m + 1) (nuOf lam)) := by
    rw [← Module.finrank_eq_card_basis b0, Formalism.L2.GlobalTheoryTheory.LemB.finrank_weylZ _ hν]
  let b := b0.reindex (Fintype.equivFinOfCardEq hcard)
  have hli := Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.weyl_basis_lin_indep_field (le_refl (m + 1)) (nuOf lam) hν Kf b
  have hd : g.det ^ (-(lam (Fin.last m))) ≠ 0 := zpow_ne_zero _ hg.ne_zero
  let φ : MvPolynomial (Fin (m + 1) × Fin (m + 1)) Kf →ₗ[Kf] MvPolynomial (Fin (m + 1) × Fin (m + 1)) Kf :=
    (g.det ^ (-(lam (Fin.last m)))) • (rowAct Kf (n := m + 1) g⁻¹).toLinearMap
  have hφ : LinearMap.ker φ = ⊥ := by
    rw [LinearMap.ker_eq_bot']
    intro x hx
    have h1 : rowAct Kf g⁻¹ x = 0 := (smul_eq_zero.1 hx).resolve_left hd
    rw [← rowAct_inv_right Kf _ _ g hg x, h1, map_zero]
  refine ⟨_, hli.map' φ hφ, ?_⟩
  rw [Formalism.L2.G.Cmp.dw_eq hinj m lam hlam g hg]
  have e1 : deltaL O Kf (m + 1) (nuOf lam) g =
      ((weyl O (m + 1) (m + 1) le_rfl (nuOf lam)).map (mapAlgHom (Algebra.ofId O Kf)).toLinearMap).map
        ((rowAct Kf (n := m + 1) g⁻¹).toLinearMap.restrictScalars O) := by
    ext x
    constructor
    · intro hx
      exact ⟨_, Submodule.mem_comap.1 hx, rowAct_inv_left Kf _ _ g hg x⟩
    · rintro ⟨y, hy, hyx⟩
      have h1 : rowAct Kf g⁻¹ y = x := hyx
      have h2 : rowAct Kf g x = y := by rw [← h1, rowAct_inv_right Kf _ _ g hg]
      refine Submodule.mem_comap.2 ?_
      rw [LinearMap.restrictScalars_apply, AlgHom.toLinearMap_apply, h2]
      exact hy
  rw [deltaLTw, e1, ← span_map_weyl O (m + 1) (nuOf lam) b, Submodule.map_span, Submodule.map_span, Submodule.map_span,
    ← Set.range_comp, ← Set.range_comp, ← Set.range_comp]
  congr 2
  funext i
  show (g.det ^ (-(lam (Fin.last m)))) • rowAct Kf (n := m + 1) g⁻¹ (map (Int.castRingHom Kf) (b i).1) =
    (g.det ^ (-(lam (Fin.last m)))) • rowAct Kf (n := m + 1) g⁻¹
      (map (algebraMap O Kf) (map (Int.castRingHom O) (b i).1))
  rw [map_map, Subsingleton.elim ((algebraMap O Kf).comp (Int.castRingHom O)) (Int.castRingHom Kf)]

theorem card_ssIdx_lamAt {n' m : ℕ} (lam0 : Fin n' → Fin (m + 1) → ℤ) (hdom : IsDominant lam0) (s : Fin n') :
    Nat.card (ssIdx (m + 1) (m + 1) (nuOf (lamAt lam0 s))) = Nat.card (ssIdx (m + 1) (m + 1) (nuOf (lam0 s))) := by
  have key : ∀ lam : Fin (m + 1) → ℤ, Antitone lam →
      ((Nat.card (ssIdx (m + 1) (m + 1) (nuOf lam)) : ℕ) : ℚ) = Formalism.CountingSumsFrames.weylDim (m + 1) lam := by
    intro lam hlam
    rw [card_ssIdx, Formalism.MainNotions.TestSideCounting.dGT_weylDim _ _ (fun a b hab => by exact_mod_cast toNat_antitone lam hlam hab)]
    have : (fun t => ((nuOf lam t : ℕ) : ℤ)) = fun t => lam t + (-lam (Fin.last m)) :=
      funext (Formalism.MainNotions.TestSideCounting.nuOf_cast lam hlam)
    rw [this, Formalism.MainNotions.Pf14.weylDim_shift]
  apply Nat.cast_injective (R := ℚ)
  rw [key _ (lamAt_antitone' lam0 hdom s), key _ (hdom s)]
  unfold lamAt
  split_ifs
  · rfl
  · exact Formalism.MainNotions.Pf14.weylDim_dual _ _

variable {p : ℕ}

theorem exists_basis_HtupW (G : GAtP p) [IsFractionRing G.O G.Kf] [CharZero G.Kf] (L : G.P.Tup)
    (hL : G.P.IsLatTup L) :
    ∃ Q : (∀ x : (Σ v : Fin G.P.nV, Fin (G.P.n' v)),
        Fin (Nat.card (ssIdx (G.P.m + 1) (G.P.m + 1) (nuOf (lamAt (G.P.lam0 x.1) x.2))))) → G.P.Xsp,
      LinearIndependent G.O Q ∧ Submodule.span G.O (Set.range Q) = G.P.HtupW L := by
  classical
  have hinj : Function.Injective (algebraMap G.O G.Kf) := IsFractionRing.injective G.O G.Kf
  have hB := fun (v : Fin G.P.nV) (s : Fin (G.P.n' v)) =>
    exists_basis_Dl0 hinj G.P.m (lamAt (G.P.lam0 v) s) (lamAt_antitone' _ (G.P.dom v) s) _
      (LatticeSystems.je_extO_lat G v s.val (L v) (hL v))
  choose B b1 b2 using hB
  have := LatticeSystems.jr_KK G.Kf
  obtain ⟨hli, -⟩ := tensorBasis G.Kf G.Kf (Σ v : Fin G.P.nV, Fin (G.P.n' v)) (G.P.m + 1) (G.P.m + 1) _
    (fun x => Submodule.span G.Kf (Set.range (B x.1 x.2))) (fun x => B x.1 x.2) (fun x => b1 x.1 x.2) (fun _ => rfl)
  have hli2 := hli.map' (rename (LatticeSystems.jr_psi G) : _ →ₐ[G.Kf] G.P.Xsp).toLinearMap
    (LinearMap.ker_eq_bot.2 (rename_injective _ (LatticeSystems.jr_psi_inj G)))
  have hli3 : LinearIndependent G.O _ := hli2.restrict_scalars
    (by intro a b hab; apply hinj; simpa [Algebra.smul_def] using hab)
  have hQ : ∀ i : (∀ x : (Σ v : Fin G.P.nV, Fin (G.P.n' v)),
        Fin (Nat.card (ssIdx (G.P.m + 1) (G.P.m + 1) (nuOf (lamAt (G.P.lam0 x.1) x.2))))),
      rename (LatticeSystems.jr_psi G) (∏ x, blockEmb G.Kf x (B x.1 x.2 (i x))) =
        ∏ v, G.P.vEmb v (∏ s, blockEmb G.Kf s (B v s (i ⟨v, s⟩))) := by
    intro i
    simp only [map_prod]
    rw [Fintype.prod_sigma]
    refine Finset.prod_congr rfl fun v _ => Finset.prod_congr rfl fun s _ => ?_
    unfold blockEmb Places.vEmb
    rw [rename_rename, rename_rename]
    rfl
  have hloc : ∀ v, Submodule.span G.O (Set.range fun i : (∀ s : Fin (G.P.n' v),
        Fin (Nat.card (ssIdx (G.P.m + 1) (G.P.m + 1) (nuOf (lamAt (G.P.lam0 v) s))))) =>
        ∏ s, blockEmb G.Kf s (B v s (i s))) =
      HtenW G.O (G.P.lam0 v) (fun s => extO G.O (G.P.ι v) (G.P.σ v) s.val (L v)) := fun v =>
    (tensorBasis G.O G.Kf (Fin (G.P.n' v)) (G.P.m + 1) (G.P.m + 1) _ _ (B v)
      (fun s => (b1 v s).restrict_scalars (by intro a b hab; apply hinj; simpa [Algebra.smul_def] using hab))
      (b2 v)).2
  refine ⟨_, hli3, le_antisymm ?_ ?_⟩
  · rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    refine Submodule.subset_span ⟨fun v => ∏ s, blockEmb G.Kf s (B v s (i ⟨v, s⟩)), fun v => ?_, hQ i⟩
    exact (hloc v).le (Submodule.subset_span ⟨fun s => i ⟨v, s⟩, rfl⟩)
  · unfold Places.HtupW Places.tenV
    rw [Submodule.span_le]
    rintro _ ⟨F, hF, rfl⟩
    refine Formalism.BasicNotions.Examples₂.NZ.prod_mem_of_span (R := G.O) (fun v => (G.P.vEmb v).toLinearMap.restrictScalars G.O) _ _
      (fun f hf => ?_) F (fun v => (hloc v).ge (hF v))
    choose I hI using hf
    refine Submodule.subset_span ⟨fun x => I x.1 x.2, ?_⟩
    refine (hQ _).trans (Finset.prod_congr rfl fun v _ => ?_)
    rw [← hI v]
    rfl

theorem actHW (G : GAtP p) (c : G.comp) : (G.lev c).ActHW := by
  have h1 : ∀ (γ : (G.lev c).Γ) (L : G.P.Tup), G.P.IsLatTup L → ∀ x ∈ G.P.HtupW L,
      (G.lev c).actX γ x ∈ G.P.HtupW ((G.lev c).smul γ L) := by
    intro γ L hL x hx
    have h := Submodule.smul_mem _ (((G.lev c).χ γ)⁻¹ : G.Oˣ).1 (Formalism.L2.G.Cmp.equivSys_HtupW G c γ L hL x hx)
    rwa [smul_smul, Units.inv_mul, one_smul] at h
  intro γ L hL
  apply le_antisymm
  · rintro _ ⟨x, hx, rfl⟩
    exact h1 γ L hL x hx
  · intro y hy
    have h := h1 γ⁻¹ _ (isLatTup_smul _ γ hL) y hy
    rw [← smul_mul, inv_mul_cancel, smul_one] at h
    refine ⟨_, h, ?_⟩
    show (G.lev c).actX γ ((G.lev c).actX γ⁻¹ y) = y
    rw [← actX_mul, mul_inv_cancel, actX_one]

theorem d_eq_of_classes (G : GAtP p) [IsFractionRing G.O G.Kf] [CharZero G.Kf] (htriv : G.TrivStab)
    {X : Type} [Fintype X] (cl : G.comp → G.P.Tup → X)
    (hiff : ∀ i i' L L', G.P.IsLatTup L → G.P.IsLatTup L' →
      (cl i L = cl i' L' ↔ i = i' ∧ ∃ γ : (G.lev i).Γ, L' = (G.lev i).smul γ L))
    (hsurj : ∀ x, ∃ i L, G.P.IsLatTup L ∧ cl i L = x) :
    G.d = Fintype.card X * ∏ x : (Σ v : Fin G.P.nV, Fin (G.P.n' v)),
      Nat.card (ssIdx (G.P.m + 1) (G.P.m + 1) (nuOf (G.P.lam0 x.1 x.2))) := by
  classical
  choose idx tup hlat hcl using hsurj
  have hr : ∀ c, IsReps (G.lev c) (fun x : {x : X // idx x = c} => tup x.1) := by
    intro c
    refine ⟨fun x => hlat x.1, fun L hL => ?_, fun x y γ h => ?_⟩
    · obtain ⟨h1, γ, h2⟩ := (hiff _ _ _ _ (hlat (cl c L)) hL).1 (hcl (cl c L))
      generalize cl c L = x at h1 γ h2
      subst h1
      exact ⟨⟨x, rfl⟩, γ, h2⟩
    · obtain ⟨x, rfl⟩ := x
      obtain ⟨y, hy⟩ := y
      apply Subtype.ext
      show x = y
      rw [← hcl x, ← hcl y]
      exact (hiff _ _ _ _ (hlat x) (hlat y)).2 ⟨hy.symm, γ, h.symm⟩
  rw [d_eq_card_mul G (IsFractionRing.injective G.O G.Kf) htriv (actHW G) _ hr ?_ _ ?_, ← Fintype.card_sigma,
    Fintype.card_congr (Equiv.sigmaFiberEquiv idx)]
  · intro c x
    obtain ⟨Q, -, hQ⟩ := exists_basis_HtupW G _ (hlat x.1)
    rw [← hQ]
    exact Submodule.fg_span (Set.finite_range _)
  · intro c x
    obtain ⟨Q, hli, hQ⟩ := exists_basis_HtupW G _ (hlat x.1)
    rw [← hQ, finrank_span_eq_card hli, Fintype.card_pi]
    refine Finset.prod_congr rfl fun y _ => ?_
    rw [Fintype.card_fin, card_ssIdx_lamAt _ (G.P.dom y.1)]

theorem card_ssIdx_natW {N m : ℕ} (h : m + 1 = N) (lam : Formalism.BasicNotions.DomWeight N) (l : Fin (m + 1) → ℤ)
    (hl : ∀ i, l i = lam.w (Fin.cast h i)) :
    Nat.card (ssIdx (m + 1) (m + 1) (nuOf l)) = Nat.card (ssIdx N N lam.natW) := by
  subst h
  have : nuOf l = lam.natW := by
    funext t
    simp only [nuOf, Formalism.BasicNotions.DomWeight.natW, Formalism.BasicNotions.DomWeight.detShift, hl, dif_pos (Nat.succ_pos m)]
    rfl
  rw [this]

end General

section Record

open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.G Formalism.L2.Forms GlobalTheory.Mem.LocalPack

attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.BasicNotions.factResChar

set_option maxHeartbeats 2000000 in

theorem locPack_d_eq (D : D7) (L0 : LevelData D) (u : D.what₂.Word) (T : Forms0 D u) (w : D.what₂.places.Pl)
    (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)) (X : LocPack D u (L0 u) (D.what₂.places.resChar w))
    (r e : ℕ) : (X.gat r e).d = Module.finrank ℂ (D.mem u).A.Mu0 := by
  have hF : IsFractionRing (X.gat r e).O (X.gat r e).Kf := X.hS.frac_O
  have hC : CharZero (X.gat r e).Kf := charZero_of_setting X.hS
  have hH := isHyperbolicAt_rec_of_placeIdentification D u w hg X.I
  have hdet := isUnit_det_gram0 D.sp
  rw [Formalism.L2.GlobalTheoryTheory.LemB.finrank_forms_level_zero T (Triv.stabZero_rec D L0 u),
    d_eq_of_classes (X.gat r e)
      (Cmp.trivStab X.hS r _ _ (k_pred D.R) X.I X.ψ e hdet hH (Triv.trivStabU_rec D L0 u))
      (fun i L => Cmp.clsR (k_pred D.R) X.I hdet i L)
      (fun i i' L L' h h' => Cmp.clsR_iff X.hS r _ _ (k_pred D.R) X.I X.ψ e hdet hH i i' L L' h h')
      (fun c => Cmp.clsR_surj X.hS r _ _ (k_pred D.R) X.I X.ψ e hdet hH c)]
  congr 1
  refine Fintype.prod_equiv (gatRec_pos D u _ X.hS r (L0 u) X.I X.ψ (repP (L0 u) _) e) _ _ fun x => ?_
  exact card_ssIdx_natW ((k_pred D.R).trans (rank_eq_first_level D.R)) _ _ fun _ => rfl

theorem pack_d_eq : ∀ (D : D7) (L0 : LevelData D) (T : ∀ u : D.what₂.Word, Forms0 D u), (∀ u, Joint0 L0 u (T u)) →
    ∀ (u : D.what₂.Word) (w : D.what₂.places.Pl) (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w))
      (I : LocId (L0 u) (D.what₂.places.resChar w) (nOrb (zH D.R.toFrame (hP D (D.what₂.places.resChar w))))
        (WQ (D.what₂.places.resChar w) (frobOrder D (D.what₂.places.resChar w)))
        (QQ (D.what₂.places.resChar w) (frobOrder D (D.what₂.places.resChar w))))
      (ψ : Formalism.L2.Herm.awayFrom₂ (L0 u) (D.what₂.places.resChar w) →*
        (ORec D w (frobOrder D (D.what₂.places.resChar w)))ˣ) (r e : ℕ),
      ((pack D u (L0 u) w hg.2.1 (frobOrder_spec D hg).1 (frobOrder_spec D hg).2 I ψ).gat r e).d =
        Module.finrank ℂ (D.mem u).A.Mu0 :=
  fun D L0 T _ u w hg _ _ r e => locPack_d_eq D L0 u (T u) w hg _ r e

end Record

end GlobalTheory.ClassRank
