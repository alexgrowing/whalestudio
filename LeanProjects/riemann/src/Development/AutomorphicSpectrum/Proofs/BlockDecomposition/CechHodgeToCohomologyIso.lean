import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.DifferentialFormsCech.GlobalDifferentialForms.PullHEq
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.DifferentialFormsCech.HdgAffIso
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.GrCechFin
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.Imports
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SerreClassOfCechSpectralSequence
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CechDoubleComplexMapStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DoubleComplexDegenerateColumnIsoStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DoubleComplexLeadSurjectiveStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DoubleComplexMapLeadCompatStatement
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris DividedPowers GlobalTheory.CechDR GlobalTheory.HodgeCoh CrystallineSemistableComparison CrystallineSemistableComparison.Pb CrystallineSemistableComparison.Om CrystallineSemistableComparison.Om.Glob GlobalTheory.CompanionTheory.CechSerre
universe w

noncomputable section

namespace GlobalTheory.CompanionTheory.CechSerre

variable {R : Type} [CommRing R]

def colHMap {K L : DCx.{1} R} (φ : DCx.Hom K L (RingHom.id R)) (q : ℕ) :
    Cx.Hom (colH K q) (colH L q) (RingHom.id R) where
  f p := (φ.col p).mapH q
  comm p x := by
    obtain ⟨a, ha, rfl⟩ := (P.cls_surj (K.col p) q).1 x
    have h1 : (K.col (p + 1)).d q ((colMap K p).f q a) = 0 := by
      rw [(colMap K p).comm, ha, map_zero]
    have h2 : (L.col p).d q ((φ.col p).f q a) = 0 := by
      rw [(φ.col p).comm, ha, map_zero]
    have h3 : (L.col (p + 1)).d q ((colMap L p).f q ((φ.col p).f q a)) = 0 := by
      rw [(colMap L p).comm, h2, map_zero]
    have h4 : (L.col (p + 1)).d q ((φ.col (p + 1)).f q ((colMap K p).f q a)) = 0 := by
      rw [(φ.col (p + 1)).comm, h1, map_zero]
    change (colMap L p).mapH q ((φ.col p).mapH q _) = (φ.col (p + 1)).mapH q ((colMap K p).mapH q _)
    rw [P.mapH_cls _ q a ha h2, P.mapH_cls _ q _ h2 h3, P.mapH_cls _ q a ha h1, P.mapH_cls _ q _ h1 h4]
    have e : (colMap L p).f q ((φ.col p).f q a) = (φ.col (p + 1)).f q ((colMap K p).f q a) := φ.ch p q a
    exact ((P.cls_surj (L.col (p + 1)) q).2.2.1 _ _ h3 h4).2 (by rw [e, sub_self]; exact Submodule.zero_mem _)

variable {C : Type 1} [Category.{0} C]

theorem restr_bij (F : C ⥤ ModuleCat.{0} R) (n : ℕ) :
    Function.Bijective ((CH.Mor.restrict F (CategoryOfElements.π ((Functor.const C).obj PUnit.{1}))).hom.mapH n) := by
  let E : C ⥤ Type := (Functor.const C).obj PUnit.{1}
  let G : C ⥤ E.Elements :=
    { obj := fun T => ⟨T, PUnit.unit⟩
      map := fun φ => ⟨φ, rfl⟩ }
  refine P.mapH_bij _ (fun k => ⟨fun x y h => ?_, fun y => ?_⟩) n
  · funext c
    exact congrFun h (c ⋙ G)
  · exact ⟨fun c => y (c ⋙ G), funext fun s => rfl⟩

variable {ι : Type}

def eTot (F : C ⥤ ModuleCat.{0} R) (U : ι → ObjectProperty C) (hU : ∀ α, Cosieve (U α))
    (hc : ∀ T, ∃ α, U α T) (n : ℕ) : CH.H F n ≃ₗ[R] (dbl U hU F).tot.H n :=
  (LinearEquiv.ofBijective _ (restr_bij F n)).trans
    (LinearEquiv.ofBijective _ (P.cech_desc (idxπ U hU) F (fun T x => by
      obtain ⟨α, hα⟩ := hc T
      exact ⟨⟨α, hα⟩, rfl⟩) n))

theorem eTot_apply (F : C ⥤ ModuleCat.{0} R) (U : ι → ObjectProperty C) (hU : ∀ α, Cosieve (U α))
    (hc : ∀ T, ∃ α, U α T) (n : ℕ) (x : CH.H F n) :
    eTot F U hU hc n x = (CH.cechAugRow (idxπ U hU) F).edge.mapH n
      ((CH.Mor.restrict F (CategoryOfElements.π ((Functor.const C).obj PUnit.{1}))).hom.mapH n x) := rfl

theorem col_sub (F : C ⥤ ModuleCat.{0} R) (U : ι → ObjectProperty C) (hU : ∀ α, Cosieve (U α)) (a : ℕ)
    (hv : ∀ n (i : Fin (n + 1) → ι) r, r ≠ a → Subsingleton (HU F (capT U i) r)) (p q : ℕ) (hq : q ≠ a) :
    Subsingleton (((dbl U hU F).col p).H q) := by
  have := fun i => hv p i q hq
  exact (colCmp_bij U hU F p q).1.subsingleton

def eRow (F : C ⥤ ModuleCat.{0} R) (U : ι → ObjectProperty C) (hU : ∀ α, Cosieve (U α)) (a : ℕ)
    (hv : ∀ n (i : Fin (n + 1) → ι) r, r ≠ a → Subsingleton (HU F (capT U i) r)) (j : ℕ) :
    (dbl U hU F).tot.H (a + j) ≃ₗ[R] (colH (dbl U hU F) a).H j :=
  Classical.choose (GlobalTheory.T.double_complex_degenerate_column_iso (dbl U hU F) a (fun p q hq => col_sub F U hU a hv p q hq) j)

theorem eRow_clsZ (F : C ⥤ ModuleCat.{0} R) (U : ι → ObjectProperty C) (hU : ∀ α, Cosieve (U α)) (a : ℕ)
    (hv : ∀ n (i : Fin (n + 1) → ι) r, r ≠ a → Subsingleton (HU F (capT U i) r)) (j : ℕ)
    (z : Zf (dbl U hU F) (a + j) j) :
    eRow F U hU a hv j (clsZ (dbl U hU F) (a + j) j z) = leadE (dbl U hU F) j a z :=
  Classical.choose_spec (GlobalTheory.T.double_complex_degenerate_column_iso (dbl U hU F) a (fun p q hq => col_sub F U hU a hv p q hq) j) z

def eCol (F : C ⥤ ModuleCat.{0} R) (U : ι → ObjectProperty C) (hU : ∀ α, Cosieve (U α)) (a j : ℕ) :
    (colH (dbl U hU F) a).H j ≃ₗ[R] (CrystallineSemistableComparison.Pb.cechH F U a).cx.H j :=
  LinearEquiv.ofBijective _ (P.mapH_bij (colCmp U hU F a) (fun p => colCmp_bij U hU F p a) j)

theorem eCol_cls (F : C ⥤ ModuleCat.{0} R) (U : ι → ObjectProperty C) (hU : ∀ α, Cosieve (U α)) (a j : ℕ)
    (x : (colH (dbl U hU F) a).X j) (hx : (colH (dbl U hU F) a).d j x = 0)
    (h : (CrystallineSemistableComparison.Pb.cechH F U a).cx.d j ((colCmp U hU F a).f j x) = 0) :
    eCol F U hU a j ((colH (dbl U hU F) a).cls x hx) = (CrystallineSemistableComparison.Pb.cechH F U a).cx.cls _ h :=
  P.mapH_cls _ j x hx h

def eDeg (F : C ⥤ ModuleCat.{0} R) (U : ι → ObjectProperty C) (hU : ∀ α, Cosieve (U α))
    (hc : ∀ T, ∃ α, U α T) (a : ℕ)
    (hv : ∀ n (i : Fin (n + 1) → ι) r, r ≠ a → Subsingleton (HU F (capT U i) r)) (j : ℕ) :
    CH.H F (a + j) ≃ₗ[R] (CrystallineSemistableComparison.Pb.cechH F U a).cx.H j :=
  (eTot F U hU hc (a + j)).trans ((eRow F U hU a hv j).trans (eCol F U hU a j))

theorem eDeg_apply (F : C ⥤ ModuleCat.{0} R) (U : ι → ObjectProperty C) (hU : ∀ α, Cosieve (U α))
    (hc : ∀ T, ∃ α, U α T) (a : ℕ)
    (hv : ∀ n (i : Fin (n + 1) → ι) r, r ≠ a → Subsingleton (HU F (capT U i) r)) (j : ℕ) (x : CH.H F (a + j)) :
    eDeg F U hU hc a hv j x = eCol F U hU a j (eRow F U hU a hv j (eTot F U hU hc (a + j) x)) := rfl

theorem cech_deg : ∀ (R : Type) [CommRing R], ∃ e : ∀ {C : Type 1} [Category.{0} C] (F : C ⥤ ModuleCat.{0} R) {ι : Type}
    (U : ι → ObjectProperty C), (∀ α, Cosieve (U α)) → (∀ T, ∃ α, U α T) → ∀ a : ℕ,
    (∀ n (i : Fin (n + 1) → ι) r, r ≠ a → Subsingleton (HU F (capT U i) r)) → ∀ j : ℕ,
      CH.H F (a + j) ≃ₗ[R] (CrystallineSemistableComparison.Pb.cechH F U a).cx.H j,
    ∀ {C C' : Type 1} [Category.{0} C] [Category.{0} C'] (F : C ⥤ ModuleCat.{0} R) (F' : C' ⥤ ModuleCat.{0} R) {ι ι' : Type}
      (U : ι → ObjectProperty C) (U' : ι' → ObjectProperty C') (hU : ∀ α, Cosieve (U α)) (hc : ∀ T, ∃ α, U α T)
      (hU' : ∀ α, Cosieve (U' α)) (hc' : ∀ T, ∃ α, U' α T) (a : ℕ)
      (hv : ∀ n (i : Fin (n + 1) → ι) r, r ≠ a → Subsingleton (HU F (capT U i) r))
      (hv' : ∀ n (i : Fin (n + 1) → ι') r, r ≠ a → Subsingleton (HU F' (capT U' i) r)) (m : CH.Mor F F' (RingHom.id R))
      (τ : ι' → ι) (hτ : ∀ α T, U' α T → U (τ α) (m.G.obj T)) (j : ℕ) (c : (CrystallineSemistableComparison.Pb.cechH F U a).X j)
      (h0 : (CrystallineSemistableComparison.Pb.cechH F U a).cx.d j c = 0)
      (h1 : (CrystallineSemistableComparison.Pb.cechH F' U' a).cx.d j (fun i => (morU m (U := capT U (τ ∘ i)) (U' := capT U' i)
        fun T hT k => hτ (i k) T (hT k)).pull a (c (τ ∘ i))) = 0),
      m.pull (a + j) ((e F U hU hc a hv j).symm ((CrystallineSemistableComparison.Pb.cechH F U a).cx.cls c h0)) =
        (e F' U' hU' hc' a hv' j).symm ((CrystallineSemistableComparison.Pb.cechH F' U' a).cx.cls _ h1) := by
  intro R _
  refine ⟨fun F _ U hU hc a hv j => eDeg F U hU hc a hv j, ?_⟩
  intro C C' _ _ F F' ι ι' U U' hU hc hU' hc' a hv hv' m τ hτ j c h0 h1
  obtain ⟨φ, hφ1, hφ2⟩ := GlobalTheory.T.cech_double_complex_map F F' U U' hU hU' m τ hτ
  obtain ⟨c₁, rfl⟩ := (colCmp_bij U hU F j a).2 c
  have hd₁ : (colH (dbl U hU F) a).d j c₁ = 0 := by
    refine (colCmp_bij U hU F (j + 1) a).1 ?_
    rw [← (colCmp U hU F a).comm, h0, map_zero]
  obtain ⟨z, hz⟩ := GlobalTheory.T.double_complex_lead_surjective (dbl U hU F) a j
    (fun p q hq => col_sub F U hU a hv p q hq.ne) ((colH (dbl U hU F) a).cls c₁ hd₁)
  have hy : (eDeg F U hU hc a hv j).symm ((CrystallineSemistableComparison.Pb.cechH F U a).cx.cls _ h0) =
      (eTot F U hU hc (a + j)).symm (clsZ (dbl U hU F) (a + j) j z) := by
    rw [LinearEquiv.symm_apply_eq, eDeg_apply, LinearEquiv.apply_symm_apply, eRow_clsZ, hz, eCol_cls F U hU a j c₁ hd₁ h0]
  obtain ⟨z', hz'1, y', hy', y₀, hy₀, e1, e2, e3⟩ := GlobalTheory.T.double_complex_map_lead_compat (dbl U hU F) (dbl U' hU' F') φ a j z
  show m.pull (a + j) ((eDeg F U hU hc a hv j).symm _) = (eDeg F' U' hU' hc' a hv' j).symm _
  rw [hy, LinearEquiv.eq_symm_apply, eDeg_apply]
  have h2 : eTot F' U' hU' hc' (a + j) (m.pull (a + j) ((eTot F U hU hc (a + j)).symm (clsZ (dbl U hU F) (a + j) j z))) =
      clsZ (dbl U' hU' F') (a + j) j z' := by
    rw [hz'1, ← LinearEquiv.apply_symm_apply (eTot F U hU hc (a + j)) (clsZ (dbl U hU F) (a + j) j z)]
    simp only [LinearEquiv.symm_apply_apply]
    exact (hφ1 _ _).symm
  rw [h2, eRow_clsZ, e2]
  have h3 : (colH (dbl U hU F) a).cls y₀ hy₀ = (colH (dbl U hU F) a).cls c₁ hd₁ := e1.symm.trans hz
  have hd₂ : (colH (dbl U' hU' F') a).d j ((colHMap φ a).f j c₁) = 0 := by
    rw [(colHMap φ a).comm, hd₁, map_zero]
  have h4 : (colH (dbl U' hU' F') a).cls y' hy' = (colH (dbl U' hU' F') a).cls _ hd₂ := by
    have hd₃ : (colH (dbl U' hU' F') a).d j ((colHMap φ a).f j y₀) = 0 := by
      rw [(colHMap φ a).comm, hy₀, map_zero]
    have h5 := congrArg ((colHMap φ a).mapH j) h3
    rw [P.mapH_cls _ j _ hy₀ hd₃, P.mapH_cls _ j _ hd₁ hd₂] at h5
    subst e3
    exact h5
  have h6 : (colCmp U' hU' F' a).f j ((colHMap φ a).f j c₁) =
      fun i => (morU m (U := capT U (τ ∘ i)) (U' := capT U' i)
        fun T hT k => hτ (i k) T (hT k)).pull a ((colCmp U hU F a).f j c₁ (τ ∘ i)) := by
    funext i
    exact hφ2 j a c₁ i
  have h7 : (CrystallineSemistableComparison.Pb.cechH F' U' a).cx.d j ((colCmp U' hU' F' a).f j ((colHMap φ a).f j c₁)) = 0 := by
    rw [(colCmp U' hU' F' a).comm, hd₂, map_zero]
  rw [h4, eCol_cls F' U' hU' a j _ hd₂ h7]
  exact ((P.cls_surj (CrystallineSemistableComparison.Pb.cechH F' U' a).cx j).2.2.1 _ _ h7 h1).2 (by rw [h6, sub_self]; exact Submodule.zero_mem _)

end GlobalTheory.CompanionTheory.CechSerre
