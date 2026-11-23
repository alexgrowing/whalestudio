import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.NGData
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.TermLoc
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.LocClosed
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RowLatticeAutomorphismsEqAdaptedModUnipotentStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsSubgroupUnitriangularPairsKeepingDoubleCosStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.TermsSameRationalInnerClassAreTranslatesStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CardStabilizerInnerDatumRowDoubleCosetStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.TermRowDoubleCosetEqIffIsometriesStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsTermTranslateByAdaptedLatticeAutomorphismsStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.BaseFrameLatticeInvariantUnderAdaptedTranslateStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MatchingTranslateSameRowDoubleCosetStatement

noncomputable section
open scoped Classical ENNReal
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.Unfold
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.OrbitCount

theorem relIndex_prod_prod {G G' : Type} [Group G] [Group G'] (H K : Subgroup G) (H' K' : Subgroup G') :
    (H.prod H').relIndex (K.prod K') = H.relIndex K * H'.relIndex K' := by
  unfold Subgroup.relIndex
  rw [← Subgroup.index_prod,
    ← Subgroup.index_comap_of_surjective ((H.subgroupOf K).prod (H'.subgroupOf K'))
      (f := (Subgroup.prodEquiv K K').toMonoidHom) (Subgroup.prodEquiv K K').surjective]
  congr 1

theorem card_image_eq_relIndex {Γ α : Type} [Group Γ] (P B : Subgroup Γ) (f : Γ → α)
    (hf : ∀ p ∈ P, ∀ q ∈ P, f p = f q ↔ p⁻¹ * q ∈ B) :
    Nat.card (f '' (P : Set Γ)) = B.relIndex P := by
  unfold Subgroup.relIndex Subgroup.index
  symm
  refine Nat.card_congr (Equiv.ofBijective
    (Quotient.lift (s := QuotientGroup.leftRel (B.subgroupOf P))
      (fun p : P => (⟨f p, p, p.2, rfl⟩ : f '' (P : Set Γ))) ?_) ⟨?_, ?_⟩)
  · intro a b h
    have h' := QuotientGroup.leftRel_apply.mp h
    apply Subtype.ext
    exact (hf a a.2 b b.2).2 (by simpa [Subgroup.mem_subgroupOf] using h')
  · intro x y hxy
    induction x using Quotient.inductionOn with | h a => ?_
    induction y using Quotient.inductionOn with | h b => ?_
    apply Quotient.sound
    apply QuotientGroup.leftRel_apply.mpr
    have := congrArg Subtype.val hxy
    simp only [Quotient.lift_mk] at this
    simpa [Subgroup.mem_subgroupOf] using (hf a a.2 b b.2).1 this
  · rintro ⟨_, p, hp, rfl⟩
    exact ⟨Quotient.mk _ ⟨p, hp⟩, rfl⟩

theorem lrel_refl {D : D7} {T T' : D.host.E} (F : LFlag (VS D) D.R.rS T) (F' : LFlag (VS D) D.R.rS T') (Λ : LV D) :
    LRel F F' Λ Λ := by
  refine ⟨1, ⟨(Formalism.HermitianLatticesTheory.isom (VS D).hT).one_mem, fun a => rfl, fun a => rfl⟩, ?_⟩
  congr 1
  simp [Formalism.HermitianLatticesTheory.gmap]

end GlobalTheory.OrbitCount

namespace GlobalTheory.OrbitCount

theorem orbit_count : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word), ∀ (F : LFlag (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E)) (F' : LFlag (VS D) D.R.rS ((Tu D u' : ℕ) : D.host.E)) (w : Point D.host.E (D.R.rS + 1)), ZhatOM (ZhatL F F') = ptMat w → Gval F F' ≠ 0 → ∀ (t₀ : TauC Y u u') (Λ₀ : LV D), TG F F' t₀ Λ₀ → ∀ K, K = {κ | ∃ (t : TauC Y u u') (Λ₁ : LV D), TG F F' t Λ₁ ∧ LRel F F' Λ₀ Λ₁ ∧ key t = κ} → K.Finite ∧ (∀ κ ∈ K, ∃ t : TauC Y u u', TG F F' t Λ₀ ∧ key t = κ) ∧ (∀ (t : TauC Y u u') (Λ₁ : LV D), TG F F' t Λ₁ → LRel F F' Λ₀ Λ₁ → wt t = wt t₀) ∧ (K.encard : ℝ≥0∞) * ENNReal.ofReal (wt t₀ ^ 2) = (((stabL F F' Λ₀).encard : ℝ≥0∞))⁻¹ := by
  intro D X Y u u' F F' w hw hG t₀ Λ₀ h₀ K hK
  obtain ⟨A, N, hA, hN, hNA, hNn, hiA, hcA⟩ := GlobalTheory.T.rowLattice_automorphisms_eq_adapted_mod_unipotent D X Y u u' t₀.lam t₀.mem
  obtain ⟨A', N', hA', hN', hNA', hNn', hiA', hcA'⟩ := GlobalTheory.T.rowLattice_automorphisms_eq_adapted_mod_unipotent D X Y u' u t₀.lam' t₀.mem'
  obtain ⟨B, hB, hNB, hBiff⟩ := GlobalTheory.T.exists_subgroup_unitriangular_pairs_keeping_doubleCoset D X Y u u' t₀
  have hS := GlobalTheory.T.card_stabilizer_innerDatum_rowDoubleCoset D X Y u u' F F' w hw hG t₀ Λ₀ h₀ B N N' hB hN hN'
  have mA : ∀ a, a ∈ A ↔ a ∈ Aut0 (lf D (X.Fu u)) t₀.lam := fun a => SetLike.mem_coe.symm.trans (Set.ext_iff.mp hA a)
  have mA' : ∀ a, a ∈ A' ↔ a ∈ Aut0 (lf D (X.Fu u')) t₀.lam' := fun a => SetLike.mem_coe.symm.trans (Set.ext_iff.mp hA' a)
  have mN : ∀ a, a ∈ N ↔ a ∈ NLam t₀.lam (lf D (X.Fu u)) := fun a => SetLike.mem_coe.symm.trans (Set.ext_iff.mp hN a)
  have mN' : ∀ a, a ∈ N' ↔ a ∈ NLam t₀.lam' (lf D (X.Fu u')) := fun a => SetLike.mem_coe.symm.trans (Set.ext_iff.mp hN' a)
  set P : Subgroup (GV D × GV D) := A.prod A' with hP
  have htr : ∀ p : GV D × GV D, ∃ s : TauC Y u u', p ∈ P → (s.lam = t₀.lam ∧ s.lam' = t₀.lam' ∧
      ∃ n ∈ NLam t₀.lam (lf D (X.Fu u)), ∃ n' ∈ NLam t₀.lam' (lf D (X.Fu u')), s.lin = n * (p.1 * t₀.lin * p.2⁻¹) * n') := by
    intro p
    by_cases hp : p ∈ P
    · obtain ⟨s, h1, h2, n, hn, n', hn', h3⟩ := GlobalTheory.T.exists_term_translate_by_adapted_lattice_automorphisms D X Y u u' t₀ p.1 ((mA _).1 hp.1) p.2 ((mA' _).1 hp.2)
      exact ⟨s, fun _ => ⟨h1, h2, n, hn, n', hn', h3⟩⟩
    · exact ⟨t₀, fun h => absurd h hp⟩
  choose s hs using htr
  have hTG : ∀ p ∈ P, TG F F' (s p) Λ₀ := by
    intro p hp
    obtain ⟨h1, -, n, hn, n', hn', h3⟩ := hs p hp
    exact GlobalTheory.T.baseFrameLattice_invariant_under_adapted_translate D X Y u u' F F' t₀ (s p) Λ₀ p.1 p.2 n n' h₀ ((mA _).1 hp.1) ((mA' _).1 hp.2) hn hn' h1 h3

  have hfib : ∀ p ∈ P, ∀ q ∈ P, key (s p) = key (s q) ↔ p⁻¹ * q ∈ B := by
    intro p hp q hq
    obtain ⟨hp1, hp2, n, hn, n', hn', hpl⟩ := hs p hp
    obtain ⟨hq1, hq2, m, hm, m', hm', hql⟩ := hs q hq
    rw [GlobalTheory.T.term_row_double_coset_eq_iff_isometries D X Y u u' (s p) (s q), hp1, hq1, hp2, hq2]
    simp only [true_and]
    have ep : (s p).lin = (n * p.1) * t₀.lin * (n'⁻¹ * p.2)⁻¹ := by rw [hpl]; group
    have eq : (s q).lin = (m * q.1) * t₀.lin * (m'⁻¹ * q.2)⁻¹ := by rw [hql]; group
    have hnA : n ∈ A := hNA ((mN n).2 hn)
    have hmA : m ∈ A := hNA ((mN m).2 hm)
    have hnA' : n'⁻¹ ∈ A' := A'.inv_mem (hNA' ((mN' n').2 hn'))
    have hmA' : m'⁻¹ ∈ A' := A'.inv_mem (hNA' ((mN' m').2 hm'))
    rw [ep, eq, hBiff (n * p.1) ((mA _).1 (A.mul_mem hnA hp.1)) (m * q.1) ((mA _).1 (A.mul_mem hmA hq.1))
      (n'⁻¹ * p.2) ((mA' _).1 (A'.mul_mem hnA' hp.2)) (m'⁻¹ * q.2) ((mA' _).1 (A'.mul_mem hmA' hq.2))]
    have hx : p.1⁻¹ * (n⁻¹ * m) * p.1⁻¹⁻¹ ∈ N :=
      hNn _ (A.inv_mem hp.1) _ (N.mul_mem (N.inv_mem ((mN n).2 hn)) ((mN m).2 hm))
    have hx' : p.2⁻¹ * (n' * m'⁻¹) * p.2⁻¹⁻¹ ∈ N' :=
      hNn' _ (A'.inv_mem hp.2) _ (N'.mul_mem ((mN' n').2 hn') (N'.inv_mem ((mN' m').2 hm')))
    have hmB : (p.1⁻¹ * (n⁻¹ * m) * p.1⁻¹⁻¹, p.2⁻¹ * (n' * m'⁻¹) * p.2⁻¹⁻¹) ∈ B :=
      hNB _ ((mN _).1 hx) _ ((mN' _).1 hx')
    have heq : ((n * p.1)⁻¹ * (m * q.1), (n'⁻¹ * p.2)⁻¹ * (m'⁻¹ * q.2)) =
        (p.1⁻¹ * (n⁻¹ * m) * p.1⁻¹⁻¹, p.2⁻¹ * (n' * m'⁻¹) * p.2⁻¹⁻¹) * (p⁻¹ * q) := by
      ext <;> simp only [Prod.fst_mul, Prod.snd_mul, Prod.fst_inv, Prod.snd_inv] <;> group
    rw [heq, B.mul_mem_cancel_left hmB]

  have hKim : K = (fun p => key (s p)) '' (P : Set (GV D × GV D)) := by
    rw [hK]
    ext κ
    constructor
    · rintro ⟨t, Λ₁, ht, hrel, rfl⟩
      obtain ⟨a, ha, a', ha', hkey⟩ := GlobalTheory.T.matching_translate_same_row_double_coset D X Y u u' F F' w hw hG t₀ t Λ₀ Λ₁ h₀ ht hrel
      have hp : (a, a') ∈ P := ⟨(mA a).2 ha, (mA' a').2 ha'⟩
      obtain ⟨h1, h2, n, hn, n', hn', h3⟩ := hs (a, a') hp
      exact ⟨(a, a'), hp, hkey (s (a, a')) h1 h2 ⟨n, hn, n', hn', h3⟩⟩
    · rintro ⟨p, hp, rfl⟩
      exact ⟨s p, Λ₀, hTG p hp, lrel_refl F F' Λ₀, rfl⟩
  have hcardK : Nat.card K = B.relIndex P := by
    rw [hKim]; exact card_image_eq_relIndex P B _ hfib
  have hBP : B ≤ P := fun b hb => ⟨(mA _).2 ((hB b).1 hb).1, (mA' _).2 ((hB b).1 hb).2.1⟩
  have hNNB : N.prod N' ≤ B := fun b hb => by
    have := hNB b.1 ((mN _).1 hb.1) b.2 ((mN' _).1 hb.2)
    simpa using this
  have hprod : (N.prod N').relIndex B * B.relIndex P = Nat.card (autLz D (X.Fu u) t₀.lam) * Nat.card (autLz D (X.Fu u') t₀.lam') := by
    rw [Subgroup.relIndex_mul_relIndex _ _ _ hNNB hBP, hP, relIndex_prod_prod, hiA, hiA']
  set k := B.relIndex P with hk
  set m := (N.prod N').relIndex B with hm
  set c := Nat.card (autLz D (X.Fu u) t₀.lam) with hc
  set c' := Nat.card (autLz D (X.Fu u') t₀.lam') with hc'
  have hmk : 0 < m * k := by rw [hprod]; exact Nat.mul_pos hcA hcA'
  have hk0 : 0 < k := Nat.pos_of_mul_pos_left hmk
  have hm0 : 0 < m := Nat.pos_of_mul_pos_right hmk
  have hKfin : K.Finite := by
    have : 0 < Nat.card K := hcardK ▸ hk0
    exact Set.finite_coe_iff.mp (Nat.card_pos_iff.mp this).2
  have hSfin : (stabL F F' Λ₀).Finite := by
    have : 0 < Nat.card (stabL F F' Λ₀) := hS ▸ hm0
    exact Set.finite_coe_iff.mp (Nat.card_pos_iff.mp this).2
  have hKenc : K.encard = (k : ℕ∞) := by
    rw [← hKfin.cast_ncard_eq, ← Nat.card_coe_set_eq, hcardK]
  have hSenc : (stabL F F' Λ₀).encard = (m : ℕ∞) := by
    rw [← hSfin.cast_ncard_eq, ← Nat.card_coe_set_eq, hS]
  have hwt : ∀ (t : TauC Y u u'), t.lam = t₀.lam → t.lam' = t₀.lam' → wt t = wt t₀ := by
    intro t h1 h2
    simp only [wt, h1, h2]
  refine ⟨hKfin, ?_, ?_, ?_⟩
  · intro κ hκ
    rw [hKim] at hκ
    obtain ⟨p, hp, rfl⟩ := hκ
    exact ⟨s p, hTG p hp, rfl⟩
  · intro t Λ₁ ht hrel
    obtain ⟨h1, h2, -⟩ := GlobalTheory.T.terms_same_rational_inner_class_are_translates D X Y u u' F F' w hw hG t₀ t Λ₀ Λ₁ h₀ ht hrel
    exact hwt t h1 h2
  · have hw2 : wt t₀ ^ 2 = (c : ℝ)⁻¹ * (c' : ℝ)⁻¹ := by
      simp only [wt]
      rw [Real.sq_sqrt (by unfold wRow; positivity)]
      rfl
    rw [hKenc, hSenc, hw2, ENNReal.ofReal_mul (by positivity),
      ENNReal.ofReal_inv_of_pos (by exact_mod_cast hcA), ENNReal.ofReal_inv_of_pos (by exact_mod_cast hcA'),
      ENNReal.ofReal_natCast, ENNReal.ofReal_natCast]
    have hcc : ((c : ℝ≥0∞))⁻¹ * ((c' : ℝ≥0∞))⁻¹ = ((m : ℝ≥0∞))⁻¹ * ((k : ℝ≥0∞))⁻¹ := by
      rw [← ENNReal.mul_inv (Or.inr (ENNReal.natCast_ne_top _)) (Or.inl (ENNReal.natCast_ne_top _)),
        ← ENNReal.mul_inv (Or.inr (ENNReal.natCast_ne_top _)) (Or.inl (ENNReal.natCast_ne_top _))]
      congr 1
      exact_mod_cast hprod.symm
    simp only [ENat.toENNReal_coe]
    rw [hcc, mul_comm, mul_assoc, ENNReal.inv_mul_cancel (by exact_mod_cast hk0.ne') (ENNReal.natCast_ne_top _), mul_one]

end GlobalTheory.OrbitCount
