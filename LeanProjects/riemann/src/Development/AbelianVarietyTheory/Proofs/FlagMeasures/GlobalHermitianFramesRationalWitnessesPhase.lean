import Mathlib
import Formalism.SharpRestriction.CuspSpanNormBounds.FractionFieldToGenericStalkAlgebraMapEq
import Formalism.SharpRestriction.CuspSpanNormBounds.PsiEDef
import Development.AbelianVarietyTheory.Definitions.Foundations.IsHermND
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ComplementReferenceCompactSubgroup
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.GFrames
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MemPerpSpan
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianDoubleCosetTermBasicFacts
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.TermInvariantsIndependentOfWitnesses
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RationalExtend
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.NumberFieldLatticeDeterminedByLocalLatticesStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.StrongApproximationUnipotentStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CoordinateLatticeUniqueTermAlmostAllPlacesStatement

noncomputable section
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL NumberField IsDedekindDomain
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.HL.GlobalWit

section Local

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] {L : LocE F E} {r k : ℕ}

theorem th_mem (S : Frames L r k) : algebraMap F E S.th ∈ L.O := by
  unfold Frames.th
  split_ifs
  · rw [L.O_def]
    exact (isIntegral_algebraMap (R := 𝒪[F]) (A := F) (x := S.ϖ)).algebraMap
  · rw [map_one]
    exact L.O.one_mem

theorem th_ne (S : Frames L r k) : S.th ≠ 0 := by
  unfold Frames.th
  split_ifs
  · intro h
    exact S.ϖ_irr.ne_zero (Subtype.ext h)
  · exact one_ne_zero

theorem inTh_mem (S : Frames L r k) {Λ : Submodule L.O S.V} {x : S.V} (h : S.InTh Λ x) : x ∈ Λ := by
  obtain ⟨y, hy, rfl⟩ := h
  exact Λ.smul_mem ⟨algebraMap F E S.th, th_mem S⟩ hy

theorem inTh_add (S : Frames L r k) {Λ : Submodule L.O S.V} {x y : S.V} (hx : S.InTh Λ x)
    (hy : S.InTh Λ y) : S.InTh Λ (x + y) := by
  obtain ⟨a, ha, rfl⟩ := hx
  obtain ⟨b, hb, rfl⟩ := hy
  unfold Frames.InTh
  exact ⟨a + b, Λ.add_mem ha hb, (smul_add _ _ _).symm⟩

theorem inTh_sub (S : Frames L r k) {Λ : Submodule L.O S.V} {x y : S.V} (hx : S.InTh Λ x)
    (hy : S.InTh Λ y) : S.InTh Λ (x - y) := by
  obtain ⟨a, ha, rfl⟩ := hx
  obtain ⟨b, hb, rfl⟩ := hy
  unfold Frames.InTh
  exact ⟨a - b, Λ.sub_mem ha hb, (smul_sub _ _ _).symm⟩

private lemma hf_apply_apply_of_mem_isomG (S : Frames L r k) {u : S.GLV} (hu : u ∈ isomG L S.Hm) (x y : S.V) :
    hf L S.Hm (u x) (u y) = hf L S.Hm x y := hu x y

theorem symm_mem_of_maps (S : Frames L r k) {Λ : Submodule L.O S.V} (hsd : IsSD L S.Hm Λ) (u : S.GLV)
    (hu : u ∈ isomG L S.Hm) (hmap : ∀ x ∈ Λ, u x ∈ Λ) : ∀ y ∈ Λ, u.symm y ∈ Λ := by
  obtain ⟨-, hsd2⟩ := hsd
  intro y hy
  refine (hsd2 (u.symm y)).1 fun x hx => ?_
  rw [← hf_apply_apply_of_mem_isomG S hu x (u.symm y), LinearEquiv.apply_symm_apply]
  exact (hsd2 y).2 hy (u x) (hmap x hx)

private lemma mem_isomG_of_hf_apply_apply (S : Frames L r k) {u : S.GLV}
    (hu : ∀ x y, hf L S.Hm (u x) (u y) = hf L S.Hm x y) : u ∈ isomG L S.Hm := hu

theorem hermitianIsometry_selfDual_eq_of_thetaClose (S : Frames L r k) {Λ I : Submodule L.O S.V} (hsd : IsSD L S.Hm Λ) {m w : S.GLV}
    (hm : m ∈ isomG L S.Hm) (hw : w ∈ isomG L S.Hm) (hI : Λ = m • I)
    (h1 : ∀ x ∈ Λ, S.InTh Λ (m (w.symm x) - x)) :
    Λ = w • I ∧ ∀ x ∈ I, S.InTh Λ (m x - w x) := by
  have hu : (w.symm.trans m) ∈ isomG L S.Hm := mem_isomG_of_hf_apply_apply S fun x y => by
    have h2 := hf_apply_apply_of_mem_isomG S hw (w.symm x) (w.symm y)
    rw [LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply] at h2
    rw [LinearEquiv.trans_apply, LinearEquiv.trans_apply, hf_apply_apply_of_mem_isomG S hm, h2]
  have hmaps : ∀ x ∈ Λ, (w.symm.trans m) x ∈ Λ := fun x hx => by
    have e : (w.symm.trans m) x = (m (w.symm x) - x) + x := by
      rw [LinearEquiv.trans_apply, sub_add_cancel]
    rw [e]
    exact Λ.add_mem (inTh_mem S (h1 x hx)) hx
  have hback := symm_mem_of_maps S hsd _ hu hmaps
  have hA : Λ = w • I := by
    ext x
    rw [GlobalTheory.HL.TermBasic.mem_smul S w I x]
    constructor
    · intro hx
      have hux := hmaps x hx
      rw [hI, GlobalTheory.HL.TermBasic.mem_smul S m I] at hux
      obtain ⟨z, hz, hzx⟩ := hux
      rw [LinearEquiv.trans_apply] at hzx
      refine ⟨w.symm x, ?_, w.apply_symm_apply x⟩
      rwa [← m.injective hzx]
    · rintro ⟨z, hz, rfl⟩
      have hmz : m z ∈ Λ := by
        rw [hI, GlobalTheory.HL.TermBasic.mem_smul S m I]
        exact ⟨z, hz, rfl⟩
      have h3 := hback (m z) hmz
      rwa [LinearEquiv.symm_trans_apply, LinearEquiv.symm_symm, LinearEquiv.symm_apply_apply] at h3
  refine ⟨hA, fun x hx => ?_⟩
  have hwx : w x ∈ Λ := by
    rw [hA, GlobalTheory.HL.TermBasic.mem_smul S w I]
    exact ⟨x, hx, rfl⟩
  have h4 := h1 (w x) hwx
  rwa [LinearEquiv.symm_apply_apply] at h4

private lemma mem_isomG_of_mem_Nof (S : Frames L r k) {g : Fin (r + 1) → S.V} {n : S.GLV}
    (h : n ∈ S.Nof g) : n ∈ isomG L S.Hm := by
  unfold Frames.Nof at h
  exact (Subgroup.mem_inf.mp (Subgroup.mem_inf.mp h).1).1

variable [IsNonarchimedeanLocalField F] [CharZero F]

theorem isTermW_of_close (S : Frames L r k) {d : S.Datum} {Λ : Submodule L.O S.V} {m m' w w' : S.GLV}
    (hT : S.IsTermW d Λ m m') (hw : w ∈ S.N) (hw' : w' ∈ S.N')
    (h1 : ∀ x ∈ Λ, S.InTh Λ (m (w.symm x) - x)) (h2 : ∀ x ∈ Λ, S.InTh Λ (m' (w'.symm x) - x)) :
    S.IsTermW d Λ w w' := by
  unfold Frames.IsTermW at hT ⊢
  obtain ⟨hin, hin', hmN, hm'N, hΛ, hΛ', hfr, hg⟩ := hT
  have hmI := mem_isomG_of_mem_Nof S hmN
  have hm'I := mem_isomG_of_mem_Nof S hm'N
  have hsd : IsSD L S.Hm Λ := by
    rw [hΛ]
    exact GlobalTheory.HL.TermBasic.isSD_smul S hmI
      (GlobalTheory.HL.StdLat.stdLat_spec L r k S S.f S.es (Or.inl ⟨rfl, rfl⟩) d.1 hin).1
  obtain ⟨hA, hB⟩ := hermitianIsometry_selfDual_eq_of_thetaClose S hsd hmI (mem_isomG_of_mem_Nof S hw) hΛ h1
  obtain ⟨hA', hB'⟩ := hermitianIsometry_selfDual_eq_of_thetaClose S hsd hm'I (mem_isomG_of_mem_Nof S hw') hΛ' h2
  have hf1 : ∀ b, S.f b ∈ S.stdLat S.f S.es d.1 := fun b => by
    simpa using GlobalTheory.HL.WitIndep.frame_mem S S.f S.es (Or.inl ⟨rfl, rfl⟩) d.1 hin 1 b
  have hf2 : ∀ b, S.f' b ∈ S.stdLat S.f' S.es' d.2.1 := fun b => by
    simpa using GlobalTheory.HL.WitIndep.frame_mem S S.f' S.es' (Or.inr ⟨rfl, rfl⟩) d.2.1 hin' 1 b
  refine ⟨hin, hin', hw, hw', hA, hA', fun b => ?_, hg⟩
  have e : w' (S.f' b) - w (S.f b) =
      (m' (S.f' b) - m (S.f b) - (m' (S.f' b) - w' (S.f' b))) + (m (S.f b) - w (S.f b)) := by
    abel
  rw [e]
  exact inTh_add S (inTh_sub S (hfr b) (hB' _ (hf2 b))) (hB _ (hf1 b))

end Local

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {sig : E →ₐ[F] E}

theorem ext_symm (A : Places F E sig) {n : ℕ} (p : HeightOneSpectrum (𝓞 F))
    {g : (Fin n → E) ≃ₗ[E] (Fin n → E)} {w : (Fin n → (A.loc p).Ep) ≃ₗ[(A.loc p).Ep] (Fin n → (A.loc p).Ep)}
    (h : A.Ext p g⁻¹ w) : A.Ext p g w.symm := by
  intro x
  rw [LinearEquiv.symm_apply_eq, h (g x)]
  congr 1
  exact (g.symm_apply_apply x).symm

theorem good_places (A : Places F E sig) (r k : ℕ) (G : GFrames A r k) (hk : 4 * r + 7 ≤ k)
    (d : G.Dat) (Λ : G.Lt) (hT : G.IsTerm d Λ) :
    {p | ¬ (G.S p).IsTermW (d p) (A.lat p Λ) 1 1}.Finite := by
  obtain ⟨hL, hloc⟩ := hT
  refine ((GlobalTheory.T.numberField_lattice_determined_by_local_lattices A (k + 2 * r + 1) Λ hL).2.2.union (GlobalTheory.T.coordinateLattice_unique_term_almost_all_places A r k G hk)).subset ?_
  intro p hp
  by_contra hq
  rw [Set.mem_union, not_or] at hq
  obtain ⟨h1, h2⟩ := hq
  simp only [Set.mem_setOf_eq, ne_eq, not_not] at h1 h2 hp
  obtain ⟨-, -, -, d₀, hW, -, -, -, -, -⟩ := h2
  haveI := (A.loc p).lf
  haveI := (A.loc p).char0
  have hT0 := hloc p
  rw [h1] at hT0 hp
  have hd : d p = d₀ := by
    refine (GlobalTheory.HL.TermBasic.term_basic (A.L p) r k (G.S p) d₀ _ ?_).2.2.2.2.2.2.2 (d p) hT0
    unfold Frames.IsTerm
    exact ⟨(1, 1), hW⟩
  rw [hd] at hp
  exact hp hW

private lemma exists_mem_Ext_of_mem_rat (A : Places F E sig) {n : ℕ}
    {K : ∀ p, Subgroup ((Fin n → (A.loc p).Ep) ≃ₗ[(A.loc p).Ep] (Fin n → (A.loc p).Ep))}
    {g : (Fin n → E) ≃ₗ[E] (Fin n → E)} (h : g ∈ A.rat K) (p : HeightOneSpectrum (𝓞 F)) :
    ∃ g' ∈ K p, A.Ext p g g' := h p

theorem global_witnesses : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {sig : E →ₐ[F] E} (A : Places F E sig), ∀ (r k : ℕ) (G : GFrames A r k), 4 * r + 7 ≤ k → ∀ d Λ,
    G.IsTerm d Λ → (∃ n ∈ G.N, ∃ n' ∈ G.N', ∀ p m m', A.Ext p n m → A.Ext p n' m' →
      (G.S p).IsTermW (d p) (A.lat p Λ) m m') ∧
    ∀ m m' : ∀ p, (G.S p).GLV, (∀ p, (G.S p).IsTermW (d p) (A.lat p Λ) (m p) (m' p)) →
      G.om d Λ = ∏ᶠ p, (G.S p).psi (m p) * ((G.S p).psi' (m' p))⁻¹ := by
  intro F E _ _ _ _ _ sig A r k G hk d Λ hT
  have hfin := good_places A r k G hk d Λ hT
  obtain ⟨hL, hloc⟩ := hT
  have key : ∀ p, ∃ q : (G.S p).GLV × (G.S p).GLV, (G.S p).IsTermW (d p) (A.lat p Λ) q.1 q.2 ∧
      ((G.S p).IsTermW (d p) (A.lat p Λ) 1 1 → q = 1) := by
    intro p
    by_cases h : (G.S p).IsTermW (d p) (A.lat p Λ) 1 1
    · exact ⟨1, h, fun _ => rfl⟩
    · haveI := (A.loc p).lf
      haveI := (A.loc p).char0
      exact ⟨(G.S p).wit (d p) (A.lat p Λ),
        (GlobalTheory.HL.TermBasic.term_basic (A.L p) r k (G.S p) (d p) (A.lat p Λ) (hloc p)).2.1,
        fun h' => absurd h' h⟩
  choose q hq using key
  have hmem : ∀ p, (q p).1 ∈ (G.S p).N ∧ (q p).2 ∈ (G.S p).N' := fun p => by
    have h := (hq p).1
    unfold Frames.IsTermW at h
    exact ⟨h.2.2.1, h.2.2.2.1⟩
  have hone : ∀ p, p ∉ {p | ¬ (G.S p).IsTermW (d p) (A.lat p Λ) 1 1} → q p = 1 := fun p hp =>
    (hq p).2 (by simpa using hp)
  have hfinN : {p | ((q p).1)⁻¹ • A.lat p Λ ≠ A.lat p Λ}.Finite := hfin.subset fun p hp => by
    by_contra h
    rw [Set.mem_setOf_eq, hone p h] at hp
    exact hp (by simp)
  have hfinN' : {p | ((q p).2)⁻¹ • A.lat p Λ ≠ A.lat p Λ}.Finite := hfin.subset fun p hp => by
    by_contra h
    rw [Set.mem_setOf_eq, hone p h] at hp
    exact hp (by simp)
  have hcfin : {p | ¬ ∃ u : (𝒪[(A.loc p).Fp])ˣ, ((u : 𝒪[(A.loc p).Fp]) : (A.loc p).Fp) =
      (Units.mk0 (G.S p).th (th_ne (G.S p)) : ((A.loc p).Fp)ˣ)}.Finite := by
    refine G.gg_fin.subset fun p hp => ?_
    by_contra hg
    rw [Set.mem_setOf_eq] at hp hg
    apply hp
    refine ⟨1, ?_⟩
    rw [Units.val_mk0]
    simp [Frames.th, hg]
  obtain ⟨g, hgN, hgP⟩ := (GlobalTheory.T.strong_approximation_unipotent_alt A r k G Λ hL (fun p => Units.mk0 (G.S p).th (th_ne (G.S p)))
    hcfin (fun p => ((q p).1)⁻¹) hfinN).1 (fun p => inv_mem (hmem p).1)
  obtain ⟨g', hg'N, hg'P⟩ := (GlobalTheory.T.strong_approximation_unipotent_alt A r k G Λ hL (fun p => Units.mk0 (G.S p).th (th_ne (G.S p)))
    hcfin (fun p => ((q p).2)⁻¹) hfinN').2 (fun p => inv_mem (hmem p).2)
  refine ⟨⟨g⁻¹, inv_mem hgN, g'⁻¹, inv_mem hg'N, fun p m m' hm hm' => ?_⟩, fun m m' hmm => ?_⟩
  · haveI := (A.loc p).lf
    haveI := (A.loc p).char0
    have hmN : m ∈ (G.S p).N := by
      obtain ⟨m₀, hm₀, hext⟩ := exists_mem_Ext_of_mem_rat A (K := fun p => (G.S p).N) (inv_mem hgN) p
      rwa [((GlobalTheory.HL.RatExt.rational_extend A _ p).2.2.1 g⁻¹).unique hm hext]
    have hm'N : m' ∈ (G.S p).N' := by
      obtain ⟨m₀, hm₀, hext⟩ := exists_mem_Ext_of_mem_rat A (K := fun p => (G.S p).N') (inv_mem hg'N) p
      rwa [((GlobalTheory.HL.RatExt.rational_extend A _ p).2.2.1 g'⁻¹).unique hm' hext]
    refine isTermW_of_close (G.S p) (hq p).1 hmN hm'N (fun x hx => ?_) (fun x hx => ?_)
    · obtain ⟨y, hy, hxy⟩ := hgP p m.symm (ext_symm A p hm) x hx
      unfold Frames.InTh
      exact ⟨y, hy, hxy⟩
    · obtain ⟨y, hy, hxy⟩ := hg'P p m'.symm (ext_symm A p hm') x hx
      unfold Frames.InTh
      exact ⟨y, hy, hxy⟩
  · unfold GFrames.om
    refine finprod_congr fun p => ?_
    haveI := (A.loc p).lf
    haveI := (A.loc p).char0
    exact (GlobalTheory.HL.WitIndep.witness_independence (A.L p) r k (G.S p) (d p) (A.lat p Λ) (m p) (m' p)
      (hmm p)).1

end GlobalTheory.HL.GlobalWit
