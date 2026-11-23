import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.NGData
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.TermLoc
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.LocClosed
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.ConcreteLevelAdelicSubset
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FrameAdaptedIsometryOfFixingBothFrames
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.InnerDatumStableIffIdentificationsCompatibleStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.InnerDatumStabiliserFromAdaptedPairStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsUniqueIsometryFixingBothFramesOfFrameAdaptStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RowLatticesSameInnerDifferByRationalUnipotentStatement
open scoped Classical ENNReal
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.Unfold
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section
namespace GlobalTheory.StabCnt
open Formalism.L2.SG.Pf

variable {D : D7} {T T' : D.host.E}

theorem mul_mem_isometriesFixingBothFrames {F : LFlag (VS D) D.R.rS T} {F' : LFlag (VS D) D.R.rS T'} {h k : GV D} (hh : h ∈ H0 F F')
    (hk : k ∈ H0 F F') : h * k ∈ H0 F F' :=
  ⟨(Formalism.HermitianLatticesTheory.isom (VS D).hT).mul_mem hh.1 hk.1, fun a => by rw [le_mul_app, hk.2.1 a, hh.2.1 a],
    fun a => by rw [le_mul_app, hk.2.2 a, hh.2.2 a]⟩

theorem principalPolarisation_exists_unique_section (F : LFlag (VS D) D.R.rS T) (F' : LFlag (VS D) D.R.rS T') : (1 : GV D) ∈ H0 F F' :=
  ⟨(Formalism.HermitianLatticesTheory.isom (VS D).hT).one_mem, fun _ => rfl, fun _ => rfl⟩

theorem nlam_iff_nrat {F0 : LFlag (VS D) D.R.rS T} {lam : LV D} {b : GV D} (hb : b ∈ Aut0 F0 lam) :
    b ∈ NLam lam F0 ↔ b ∈ NRat F0 :=
  ⟨fun h => ⟨h.1.1, h.2.1, h.2.2⟩, fun h => ⟨⟨h.1, hb.2⟩, h.2.1, h.2.2⟩⟩

section Corr

variable {F0 F : LFlag (VS D) D.R.rS T} {F0' F' : LFlag (VS D) D.R.rS T'} {γ g : GV D}

theorem s_adapt (hγ : γ ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT) (hg : Adapt g F0 F) (hg' : Adapt g (mapLF γ F0') F')
    {b₁ b₂ n n' : GV D} (hb1 : Adapt b₁ F0 F0) (hb2 : Adapt b₂ F0' F0') (hn : n ∈ NRat F0) (hn' : n' ∈ NRat F0')
    (he : b₁ * γ * b₂⁻¹ = n * γ * n') :
    Adapt (g * n⁻¹ * b₁ * g⁻¹) F F ∧ Adapt (g * n⁻¹ * b₁ * g⁻¹) F' F' ∧
      g * n⁻¹ * b₁ * g⁻¹ = (g * γ) * (n' * b₂) * (g * γ)⁻¹ := by
  have e1 : n⁻¹ * b₁ = γ * n' * b₂ * γ⁻¹ := by
    calc n⁻¹ * b₁ = n⁻¹ * (b₁ * γ * b₂⁻¹) * b₂ * γ⁻¹ := by group
      _ = n⁻¹ * (n * γ * n') * b₂ * γ⁻¹ := by rw [he]
      _ = γ * n' * b₂ * γ⁻¹ := by group
  have hseq : g * n⁻¹ * b₁ * g⁻¹ = (g * γ) * (n' * b₂) * (g * γ)⁻¹ := by
    calc g * n⁻¹ * b₁ * g⁻¹ = g * (n⁻¹ * b₁) * g⁻¹ := by group
      _ = g * (γ * n' * b₂ * γ⁻¹) * g⁻¹ := by rw [e1]
      _ = (g * γ) * (n' * b₂) * (g * γ)⁻¹ := by group
  have hG : Adapt (g * γ) F0' F' := adapt_mul (adapt_mapLF hγ) hg'
  refine ⟨adapt_mul (adapt_inv hg) (adapt_mul hb1 (adapt_mul (adapt_nrat (nrat_inv hn)) hg)), ?_, hseq⟩
  rw [hseq]
  exact adapt_mul (adapt_inv hG) (adapt_mul (adapt_mul hb2 (adapt_nrat hn')) hG)

theorem cong_mod {A0 A : LFlag (VS D) D.R.rS T} {a s μ n b : GV D} (ha : Adapt a A0 A) (hs : Adapt s A A)
    (hμ : μ ∈ NRat A) (hn : n ∈ NRat A0) (hb : Adapt b A0 A0) (hseq : s = a * (n * b) * a⁻¹) :
    ∀ x ∈ orth (VS D) (Xsp A), (s * μ⁻¹) x - (a * b * a⁻¹) x ∈ Xsp A := by
  intro x hx
  have e : (s * μ⁻¹) x - (a * b * a⁻¹) x = s (μ⁻¹ x - x) + a (n (b (a⁻¹ x)) - b (a⁻¹ x)) := by
    rw [hseq]
    simp only [le_mul_app, map_sub]
    abel
  rw [e]
  refine add_mem (mem_of_map_eq (adapt_xsp hs) ((nrat_inv hμ).2.2 x hx)) ?_
  refine mem_of_map_eq (adapt_xsp ha) (hn.2.2 _ ?_)
  exact mem_of_map_eq (adapt_orth hb) (symm_mem_of_map_eq (adapt_orth ha) hx)

variable (hγ : γ ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT) (hg : Adapt g F0 F) (hg' : Adapt g (mapLF γ F0') F')
  (hI : ∀ s, Adapt s F F → Adapt s F' F' → ∃! h, h ∈ H0 F F' ∧ h⁻¹ * s ∈ NRat F ∧ h⁻¹ * s ∈ NRat F')
include hγ hg hg'

include hI in
theorem corr_exists {lam lam' : LV D} {b : GV D × GV D} (hb : InB F0 F0' lam lam' γ b) :
    ∃ h, Corr F0 F F0' F' γ g b h := by
  obtain ⟨⟨n, hn, n', hn', he⟩, -⟩ := hb.2.2
  obtain ⟨hs1, hs2, -⟩ := s_adapt hγ hg hg' hb.1.1 hb.2.1.1 hn hn' he
  obtain ⟨h, ⟨hh, h1, h2⟩, -⟩ := hI _ hs1 hs2
  exact ⟨h, hh, n, hn, n', hn', he, h1, h2⟩

include hI in
theorem corr_unique {b : GV D × GV D} (hb1 : Adapt b.1 F0 F0) (hb2 : Adapt b.2 F0' F0') {h k : GV D}
    (hh : Corr F0 F F0' F' γ g b h) (hk : Corr F0 F F0' F' γ g b k) : h = k := by
  obtain ⟨hh0, n, hn, n', hn', he, h1, h2⟩ := hh
  obtain ⟨hk0, m, hm, m', hm', he2, k1, k2⟩ := hk
  obtain ⟨hs1, hs2, hseq⟩ := s_adapt hγ hg hg' hb1 hb2 hn hn' he
  obtain ⟨-, -, hteq⟩ := s_adapt hγ hg hg' hb1 hb2 hm hm' he2
  have hG : Adapt (g * γ) F0' F' := adapt_mul (adapt_mapLF hγ) hg'
  have tF : (g * m⁻¹ * b.1 * g⁻¹)⁻¹ * (g * n⁻¹ * b.1 * g⁻¹) ∈ NRat F := by
    have e : (g * m⁻¹ * b.1 * g⁻¹)⁻¹ * (g * n⁻¹ * b.1 * g⁻¹) = (g * b.1⁻¹) * (m * n⁻¹) * (g * b.1⁻¹)⁻¹ := by group
    rw [e]; exact nrat_conj (adapt_mul (adapt_inv hb1) hg) (nrat_mul hm (nrat_inv hn))
  have tF' : (g * m⁻¹ * b.1 * g⁻¹)⁻¹ * (g * n⁻¹ * b.1 * g⁻¹) ∈ NRat F' := by
    have e : (g * m⁻¹ * b.1 * g⁻¹)⁻¹ * (g * n⁻¹ * b.1 * g⁻¹) =
        ((g * γ) * b.2⁻¹) * (m'⁻¹ * n') * ((g * γ) * b.2⁻¹)⁻¹ := by rw [hseq, hteq]; group
    rw [e]; exact nrat_conj (adapt_mul (adapt_inv hb2) hG) (nrat_mul (nrat_inv hm') hn')
  obtain ⟨x, -, hu⟩ := hI _ hs1 hs2
  have ek : k⁻¹ * (g * n⁻¹ * b.1 * g⁻¹) = (k⁻¹ * (g * m⁻¹ * b.1 * g⁻¹)) * ((g * m⁻¹ * b.1 * g⁻¹)⁻¹ * (g * n⁻¹ * b.1 * g⁻¹)) := by group
  rw [hu h ⟨hh0, h1, h2⟩, hu k ⟨hk0, by rw [ek]; exact nrat_mul k1 tF, by rw [ek]; exact nrat_mul k2 tF'⟩]

theorem corr_mul {lam lam' : LV D} {b c : GV D × GV D} (hb : InB F0 F0' lam lam' γ b)
    (hc : InB F0 F0' lam lam' γ c) {h k : GV D} (hh : Corr F0 F F0' F' γ g b h)
    (hk : Corr F0 F F0' F' γ g c k) : Corr F0 F F0' F' γ g (b * c) (h * k) := by
  obtain ⟨hh0, n, hn, n', hn', he, h1, h2⟩ := hh
  obtain ⟨hk0, m, hm, m', hm', hec, k1, k2⟩ := hk
  have hk1 := (frameAdaptedIsometry_of_fixing_both_frames hk0).1
  have hk2 := (frameAdaptedIsometry_of_fixing_both_frames hk0).2
  refine ⟨mul_mem_isometriesFixingBothFrames hh0 hk0, b.1 * m * b.1⁻¹ * n, nrat_mul (nrat_conj hb.1.1 hm) hn,
    n' * (b.2 * m' * b.2⁻¹), nrat_mul hn' (nrat_conj hb.2.1.1 hm'), ?_, ?_, ?_⟩
  · show b.1 * c.1 * γ * (b.2 * c.2)⁻¹ = _
    calc b.1 * c.1 * γ * (b.2 * c.2)⁻¹ = b.1 * (c.1 * γ * c.2⁻¹) * b.2⁻¹ := by group
      _ = b.1 * (m * γ * m') * b.2⁻¹ := by rw [hec]
      _ = b.1 * m * b.1⁻¹ * (b.1 * γ * b.2⁻¹) * (b.2 * m' * b.2⁻¹) := by group
      _ = b.1 * m * b.1⁻¹ * (n * γ * n') * (b.2 * m' * b.2⁻¹) := by rw [he]
      _ = _ := by group
  · have e : (h * k)⁻¹ * (g * (b.1 * m * b.1⁻¹ * n)⁻¹ * (b * c).1 * g⁻¹) =
        (k⁻¹ * (h⁻¹ * (g * n⁻¹ * b.1 * g⁻¹)) * k⁻¹⁻¹) * (k⁻¹ * (g * m⁻¹ * c.1 * g⁻¹)) := by
      show _ = _; simp only [Prod.fst_mul]; group
    rw [e]; exact nrat_mul (nrat_conj (adapt_inv hk1) h1) k1
  · have e : (h * k)⁻¹ * (g * (b.1 * m * b.1⁻¹ * n)⁻¹ * (b * c).1 * g⁻¹) =
        (k⁻¹ * (h⁻¹ * (g * n⁻¹ * b.1 * g⁻¹)) * k⁻¹⁻¹) * (k⁻¹ * (g * m⁻¹ * c.1 * g⁻¹)) := by
      show _ = _; simp only [Prod.fst_mul]; group
    rw [e]; exact nrat_mul (nrat_conj (adapt_inv hk2) h2) k2

theorem corr_stab {lam lam' Λ : LV D} (hγl : Formalism.HermitianLatticesTheory.gmap γ lam' = lam) (hΛ : Λ = Formalism.HermitianLatticesTheory.gmap g lam)
    {b : GV D × GV D} (hb : InB F0 F0' lam lam' γ b) {h : GV D} (hh : Corr F0 F F0' F' γ g b h) :
    h ∈ stabL F F' Λ := by
  obtain ⟨hh0, n, hn, n', hn', he, h1, h2⟩ := hh
  obtain ⟨hs1, hs2, hseq⟩ := s_adapt hγ hg hg' hb.1.1 hb.2.1.1 hn hn' he
  have hG : Adapt (g * γ) F0' F' := adapt_mul (adapt_mapLF hγ) hg'
  have hh' : h = (g * n⁻¹ * b.1 * g⁻¹) * (h⁻¹ * (g * n⁻¹ * b.1 * g⁻¹))⁻¹ := by group
  refine ⟨hh0, (GlobalTheory.T.innerDatum_stable_iff_identifications_compatible D T T' F0 F F0' F' lam lam' Λ γ g h b.1 b.2 hγ hγl hg hg' hΛ hb.1 hb.2.1 hh0
    ?_ ?_).2 hb.2.2.2⟩
  · intro x hx
    rw [hh']
    exact cong_mod hg hs1 h1 (nrat_inv hn) hb.1.1 (by group) x hx
  · intro x hx
    rw [hh', show g * γ * b.2 * γ⁻¹ * g⁻¹ = (g * γ) * b.2 * (g * γ)⁻¹ by group]
    exact cong_mod hG hs2 h2 hn' hb.2.1.1 hseq x hx

include hI in
theorem corr_ker {lam lam' : LV D} {b : GV D × GV D} (hb : InB F0 F0' lam lam' γ b) {h : GV D}
    (hh : Corr F0 F F0' F' γ g b h) : h = 1 ↔ b.1 ∈ NLam lam F0 ∧ b.2 ∈ NLam lam' F0' := by
  obtain ⟨hh0, n, hn, n', hn', he, h1, h2⟩ := hh
  obtain ⟨hs1, hs2, hseq⟩ := s_adapt hγ hg hg' hb.1.1 hb.2.1.1 hn hn' he
  have hG : Adapt (g * γ) F0' F' := adapt_mul (adapt_mapLF hγ) hg'
  rw [nlam_iff_nrat hb.1, nlam_iff_nrat hb.2.1]
  constructor
  · rintro rfl
    rw [inv_one, one_mul] at h1 h2
    constructor
    · have c := nrat_conj (adapt_inv hg) h1
      have e : g⁻¹ * (g * n⁻¹ * b.1 * g⁻¹) * g⁻¹⁻¹ = n⁻¹ * b.1 := by group
      rw [e] at c
      have := nrat_mul hn c
      rwa [mul_inv_cancel_left] at this
    · rw [hseq] at h2
      have c := nrat_conj (adapt_inv hG) h2
      have e : (g * γ)⁻¹ * ((g * γ) * (n' * b.2) * (g * γ)⁻¹) * (g * γ)⁻¹⁻¹ = n' * b.2 := by group
      rw [e] at c
      have := nrat_mul (nrat_inv hn') c
      rwa [inv_mul_cancel_left] at this
  · rintro ⟨c1, c2⟩
    have sF : g * n⁻¹ * b.1 * g⁻¹ ∈ NRat F := by
      have e : g * n⁻¹ * b.1 * g⁻¹ = g * (n⁻¹ * b.1) * g⁻¹ := by group
      rw [e]; exact nrat_conj hg (nrat_mul (nrat_inv hn) c1)
    have sF' : g * n⁻¹ * b.1 * g⁻¹ ∈ NRat F' := by
      rw [hseq]; exact nrat_conj hG (nrat_mul hn' c2)
    obtain ⟨x, -, hu⟩ := hI _ hs1 hs2
    rw [hu h ⟨hh0, h1, h2⟩, hu 1 ⟨principalPolarisation_exists_unique_section F F', by rwa [inv_one, one_mul], by rwa [inv_one, one_mul]⟩]

end Corr

theorem card_of_hom {G : Type*} [Group G] {B : Subgroup (G × G)} {N N' : Subgroup G} (φ : B →* G) (S : Set G)
    (hR : ∀ h, h ∈ φ.range ↔ h ∈ S) (hK : ∀ b : B, φ b = 1 ↔ (b : G × G).1 ∈ N ∧ (b : G × G).2 ∈ N') :
    Nat.card S = (N.prod N').relIndex B := by
  have hker : φ.ker = (N.prod N').subgroupOf B := by
    ext b
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, Subgroup.mem_prod, hK]
  have e1 : Nat.card S = Nat.card φ.range :=
    Nat.card_congr (Equiv.subtypeEquivRight fun h => (hR h).symm)
  rw [e1, ← Nat.card_congr (QuotientGroup.quotientKerEquivRange φ).toEquiv, Subgroup.relIndex, ← hker]
  rfl

theorem stab_card : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word), ∀ (F : LFlag (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E)) (F' : LFlag (VS D) D.R.rS ((Tu D u' : ℕ) : D.host.E)) (w : Point D.host.E (D.R.rS + 1)), ZhatOM (ZhatL F F') = ptMat w → Gval F F' ≠ 0 → ∀ (t : TauC Y u u') (Λ : LV D), TG F F' t Λ → ∀ (B : Subgroup (GV D × GV D)) (N N' : Subgroup (GV D)), (∀ b, b ∈ B ↔ b.1 ∈ Aut0 (lf D (X.Fu u)) t.lam ∧ b.2 ∈ Aut0 (lf D (X.Fu u')) t.lam' ∧ KeyEq (lf D (X.Fu u)) (lf D (X.Fu u')) t.lam t.lin (b.1 * t.lin * b.2⁻¹)) → (N : Set (GV D)) = NLam t.lam (lf D (X.Fu u)) → (N' : Set (GV D)) = NLam t.lam' (lf D (X.Fu u')) → Nat.card (stabL F F' Λ) = (N.prod N').relIndex B := by
  intro D X Y u u' F F' w hZ hG t Λ hTG B N N' hB hN hN'
  obtain ⟨g, hg, hg', hΛ⟩ := hTG
  have hγ : t.lin ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT := t.rep.2.2.1
  have hγl : Formalism.HermitianLatticesTheory.gmap t.lin t.lam' = t.lam := t.rep.2.2.2.1
  have hg2 : Adapt g (mapLF t.lin (lf D (X.Fu u'))) F' := hg'
  have hI := GlobalTheory.T.existsUnique_isometryFixingBothFrames_of_frameAdapted D X Y u u' F F' w hZ hG
  have hB' : ∀ b, b ∈ B ↔ InB (lf D (X.Fu u)) (lf D (X.Fu u')) t.lam t.lam' t.lin b := hB
  have hf : ∀ b : B, ∃ h, Corr (lf D (X.Fu u)) F (lf D (X.Fu u')) F' t.lin g (b : GV D × GV D) h :=
    fun b => corr_exists hγ hg hg2 hI ((hB' b).1 b.2)
  let f : B → GV D := fun b => Classical.choose (hf b)
  have hfs : ∀ b : B, Corr (lf D (X.Fu u)) F (lf D (X.Fu u')) F' t.lin g (b : GV D × GV D) (f b) :=
    fun b => Classical.choose_spec (hf b)
  have hAd : ∀ b : B, Adapt (b : GV D × GV D).1 (lf D (X.Fu u)) (lf D (X.Fu u)) ∧
      Adapt (b : GV D × GV D).2 (lf D (X.Fu u')) (lf D (X.Fu u')) :=
    fun b => ⟨((hB' b).1 b.2).1.1, ((hB' b).1 b.2).2.1.1⟩
  let φ : B →* GV D := MonoidHom.mk' f fun b c =>
    corr_unique hγ hg hg2 hI (hAd (b * c)).1 (hAd (b * c)).2 (hfs (b * c))
      (corr_mul hγ hg hg2 ((hB' b).1 b.2) ((hB' c).1 c.2) (hfs b) (hfs c))
  refine card_of_hom φ _ (fun h => ⟨?_, fun hh => ?_⟩) (fun b => ?_)
  · rintro ⟨b, rfl⟩
    exact corr_stab hγ hg hg2 hγl hΛ ((hB' b).1 b.2) (hfs b)
  · have hrow : IsRowLat D (X.Fu u) t.lam := (Y.rowsOK u).1 _ t.mem
    have hrow' : IsRowLat D (X.Fu u') t.lam' := (Y.rowsOK u').1 _ t.mem'
    obtain ⟨b, hbB, hbC⟩ := GlobalTheory.T.innerDatumStabiliser_from_adapted_pair D _ _ (lf D (X.Fu u)) F (lf D (X.Fu u')) F' t.lam t.lam' Λ t.lin g h
      hγ hγl hg hg2 hΛ (fun σ hσ hL => GlobalTheory.T.row_lattices_same_inner_differ_by_rational_unipotent D _ (X.Fu u) t.lam t.lam σ hrow hrow hσ hL)
      (fun σ hσ hL => GlobalTheory.T.row_lattices_same_inner_differ_by_rational_unipotent D _ (X.Fu u') t.lam' t.lam' σ hrow' hrow' hσ hL) hh
    refine ⟨⟨b, (hB' b).2 hbB⟩, ?_⟩
    exact corr_unique hγ hg hg2 hI hbB.1.1 hbB.2.1.1 (hfs _) hbC
  · have hK := corr_ker hγ hg hg2 hI ((hB' b).1 b.2) (hfs b)
    show f b = 1 ↔ _
    rw [hK]
    constructor
    · rintro ⟨h1, h2⟩
      refine ⟨?_, ?_⟩
      · show _ ∈ (N : Set (GV D)); rw [hN]; exact h1
      · show _ ∈ (N' : Set (GV D)); rw [hN']; exact h2
    · rintro ⟨h1, h2⟩
      refine ⟨?_, ?_⟩
      · have : (b : GV D × GV D).1 ∈ (N : Set (GV D)) := h1
        rwa [hN] at this
      · have : (b : GV D × GV D).2 ∈ (N' : Set (GV D)) := h2
        rwa [hN'] at this

end GlobalTheory.StabCnt
