import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GlobalUnitaryForms.HodgeTateFromSandwich
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.TraceFormulaEigenvalues.FormsFin
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GlobalUnitaryForms.FibAbs
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GlobalUnitaryForms.FibCon
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.SymmetricFiberMasterFormula
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.SymmetricFiberTraceKernel
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.OrbitalFiberSupportFinite
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.OrbitalFiberPairCorrespondence
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.OrbitalFiberRepresentatives
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.OrbitalFiberLevelFinite
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.OrbitalFiberFixedSetConj
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.OrbitalFiberFixedSetSupport
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.OrbitalFiberHasTraceLaw
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GlobalUnitaryForms.ScalarTuples.BaseSub
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GlobalUnitaryForms.ScalarTuples.ProdChar
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GlobalUnitaryForms.ScalarTuples.ExIota
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GlobalUnitaryForms.ScalarTuples.CommOfConj
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GlobalUnitaryForms.ScalarTuples.ClassRep
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GlobalUnitaryForms.ScalarTuples.EmbAlg

noncomputable section

namespace UpperTheory.V.Z.Sym.Glob

open MulAction Fib

private lemma normal_of_center {Γ : Type} [Group Γ] {A : Subgroup Γ} (h : A ≤ Subgroup.center Γ) : A.Normal := ⟨fun n hn g => by
  rw [Subgroup.mem_center_iff.mp (h hn) g, mul_inv_cancel_right]
  exact hn⟩

private lemma stab_mk {G : Type} [Group G] (U : Subgroup G) (g : G) :
    stabilizer G (g : G ⧸ U) = U.map (MulAut.conj g).toMonoidHom := by
  ext x
  rw [mem_stabilizer_iff, Subgroup.mem_map_equiv, MulAut.conj_symm_apply, MulAction.Quotient.smul_coe, eq_comm,
    QuotientGroup.eq]
  simp [mul_assoc]

private lemma triv_act {Γ G : Type} [Group Γ] [Group G] (ι : Γ →* G) (U : Subgroup G) (z : Γ)
    (h1 : ι z ∈ Subgroup.center G) (h2 : ι z ∈ U) (y : G ⧸ U) : ι z • y = y := by
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective y
  rw [MulAction.Quotient.smul_coe, QuotientGroup.eq, smul_eq_mul, ← Subgroup.mem_center_iff.mp h1 g]
  simpa [mul_assoc] using U.inv_mem h2

private theorem glue (hM : Master) (hTr : TrKer) (hPair : Pair)
    {Γ G : Type} [Group Γ] [Group G] (ι : Γ →* G) (S U U' : Subgroup G) (Γ₁ Γ₀ : Subgroup Γ) (ι₁ : Γ₁ →* S)
    (h1 : ∀ γ, (ι₁ γ : G) = ι γ) (h2 : ∀ a b : G, a * b * a⁻¹ * b⁻¹ ∈ S) (h3 : Γ₁.Normal) (h4 : Γ₀ ≤ Subgroup.center Γ)
    (h5' : ∀ z ∈ Γ₀, ι z ∈ Subgroup.center G ∧ ι z ∈ U') (h6 : U ≤ U') (h7 : U.relIndex (U' ⊓ S) ≠ 0)
    (h8 : ∀ x : G, ∃ T : Finset S, ∀ s, ∃ h, ∃ t ∈ T, ∃ u : S, x⁻¹ * u * x ∈ U ∧ s = ι₁ h * t * u)
    (h9 : ∀ x : G, {h | x⁻¹ * ι₁ h * x ∈ U}.Finite)
    (h10 : ∃ T : Finset G, ∀ g, ∃ γ, ∃ s ∈ T, ∃ u ∈ U', g = ι γ * s * u)
    (h11' : ∀ g, Γ₀.relIndex ((U'.map (MulAut.conj g).toMonoidHom).comap ι) ≠ 0) :
    ∃ c : ℝ, 0 < c ∧ ∀ (n : ℕ) (x : Fin (n + 1) → G),
      (∀ i j γ, ∀ s ∈ S, ∀ u ∈ U', x j = ι γ * s * x i * u → i = j) → (∀ g, ∃ i γ, ∃ s ∈ S, ∃ u ∈ U', g = ι γ * s * x i * u) →
      ∀ (V : Type) [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V] (f : G → ℂ) (B : Fin (n + 1) → Base Γ₁ S V)
        (cl : Γ → ℂ) (I : Type) (δ : I → Γ) (Hi : I → Type) [∀ i, Group (Hi i)] (φ : ∀ i, Hi i →* Γ),
      (∀ u ∈ U', ∀ g, f (u⁻¹ * g * u) = f g) → (∀ g, {γ : Γ₁ | f (g⁻¹ * ι γ * g) ≠ 0}.Finite) →
      (∀ i, (B i).ι = ι₁) → (∀ i (s : S), s ∈ (B i).U ↔ (x i)⁻¹ * s * x i ∈ U) → (∀ i, (B i).ω = 1) → (∀ i, (B i).Γ₀ = ⊥) →
      (∀ i, (B i).Fin) → (∀ i, (Base.Tw.one (B i)).IsTest fun g : S => f ((x i)⁻¹ * g * x i)) →
      (∀ h γ, cl (h * γ * h⁻¹) = cl γ) → (∀ g, cl g ≠ 0 → g ∈ Γ₁) → (∀ i (γ : Γ₁), LinearMap.trace ℂ V ((B i).W γ) = cl γ) →
      (∀ i x, x ∈ (φ i).range ↔ x * δ i = δ i * x) → (∀ i i' h, δ i' = h * δ i * h⁻¹ → i = i') →
      (∀ γ g, cl γ * f (g⁻¹ * ι γ * g) ≠ 0 → ∃ i h, γ = h * δ i * h⁻¹) →
      ∑ i, LinearMap.trace ℂ (B i).Forms ((Base.Tw.one (B i)).R fun g : S => f ((x i)⁻¹ * g * x i)) =
        c * ∑ᶠ i, cl (δ i) * gqOn (ι.comp (φ i)) (Γ₀.comap (φ i)) U' fun y => f (y.out⁻¹ * ι (δ i) * y.out) := by
  classical
  have hΓ₀n : Γ₀.Normal := normal_of_center h4
  have htriv : ∀ z ∈ Γ₀, ∀ y : G ⧸ U', ι z • y = y := fun z hz y =>
    triv_act ι U' z (h5' z hz).1 (h5' z hz).2 y
  have hstab : ∀ y : G ⧸ U', Γ₀.relIndex ((stabilizer G y).comap ι) ≠ 0 := by
    intro y
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective y
    rw [stab_mk]
    exact h11' g
  obtain ⟨c, hc, hmain⟩ := hM Γ G ι S U U' Γ₁ Γ₀ ι₁ h1 h2 h3 hΓ₀n htriv h6 h7 h8 h9 h10 hstab
  refine ⟨c, hc, ?_⟩
  intro n x hdis hcov V _ _ _ f B cl I δ Hi _ φ hf hfin hBι hBU hω hΓ hBF hT hcl hcl1 htr hφ hδ hsupp
  let Φ : G → ℂ := fun g => ∑ᶠ γ : Γ, cl γ * f (g⁻¹ * ι γ * g)
  have hsub : ∀ g : G, ∑ᶠ γ : Γ₁, cl γ * f (g⁻¹ * ι γ * g) = Φ g := by
    intro g
    have hs : Function.support (fun γ => cl γ * f (g⁻¹ * ι γ * g)) ⊆ (Γ₁ : Set Γ) := by
      intro γ hγ
      exact hcl1 γ (left_ne_zero_of_mul hγ)
    show _ = ∑ᶠ γ : Γ, cl γ * f (g⁻¹ * ι γ * g)
    refine (finsum_set_coe_eq_finsum_mem (f := fun γ => cl γ * f (g⁻¹ * ι γ * g)) (Γ₁ : Set Γ)).trans ?_
    rw [finsum_mem_def, Set.indicator_eq_self.2 hs]
  have hΦl : ∀ (h : Γ) (g : G), Φ (ι h * g) = Φ g := by
    intro h g
    show ∑ᶠ γ : Γ, cl γ * f ((ι h * g)⁻¹ * ι γ * (ι h * g)) = ∑ᶠ γ : Γ, cl γ * f (g⁻¹ * ι γ * g)
    rw [← finsum_comp_equiv (MulAut.conj h).toEquiv]
    apply finsum_congr
    intro γ
    show cl (h * γ * h⁻¹) * f ((ι h * g)⁻¹ * ι (h * γ * h⁻¹) * (ι h * g)) = cl γ * f (g⁻¹ * ι γ * g)
    rw [hcl]
    congr 2
    simp only [map_mul, map_inv]
    group
  have hΦr : ∀ u ∈ U', ∀ g : G, Φ (g * u) = Φ g := by
    intro u hu g
    show ∑ᶠ γ : Γ, cl γ * f ((g * u)⁻¹ * ι γ * (g * u)) = ∑ᶠ γ : Γ, cl γ * f (g⁻¹ * ι γ * g)
    apply finsum_congr
    intro γ
    rw [← hf u hu (g⁻¹ * ι γ * g)]
    congr 2
    group
  have hM' := hmain (Fin (n + 1)) x (fun i => (B i).U) Φ hdis hcov hBU hΦl hΦr
  beta_reduce at hM'
  have hL : ∀ i, LinearMap.trace ℂ (B i).Forms ((Base.Tw.one (B i)).R fun g : S => f ((x i)⁻¹ * g * x i)) =
      gqOn ι₁ ⊥ (B i).U (fun s => Φ (↑(Quotient.out s) * x i)) := by
    intro i
    rw [hTr _ _ _ (B i) (hBF i) (hω i) (hΓ i) _ (hT i), hBι i]
    congr 1
    funext y
    rw [← hsub]
    apply finsum_congr
    intro γ
    rw [htr i γ]
    beta_reduce
    congr 2
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, h1]
    group
  have hfinP : ∀ g : G, {γ | cl γ * f (g⁻¹ * ι γ * g) ≠ 0}.Finite := by
    intro g
    refine ((hfin g).image Subtype.val).subset ?_
    intro γ hγ
    have hγ1 := hcl1 γ (left_ne_zero_of_mul hγ)
    exact ⟨⟨γ, hγ1⟩, right_ne_zero_of_mul hγ, rfl⟩
  have hP := hPair Γ G I ι Γ₀ U' cl f δ Hi φ h4 htriv hcl hf hfinP h10 hstab hφ hδ hsupp
  rw [Finset.sum_congr rfl (fun i _ => hL i), hM']
  exact congrArg (fun z => (c : ℂ) * z) hP

end UpperTheory.V.Z.Sym.Glob

namespace UpperTheory.V.Z.Sym.Glob

open NumberField IsDedekindDomain Matrix Loc MulAction Fib

private lemma dx_ext {K : Type} [Field K] {Δ : K} {g g' : DX Δ} (h : mt g = mt g') : g = g' :=
  Subtype.ext (Units.ext h)

private lemma comm_abs {G A : Type} [Group G] [CommGroup A] (d : G →* A) (a b : G) : a * b * a⁻¹ * b⁻¹ ∈ d.ker := by
  rw [MonoidHom.mem_ker, map_mul, map_mul, map_mul, map_inv, map_inv, mul_right_comm (d a), mul_inv_cancel, one_mul,
    mul_inv_cancel]

private lemma comm_mem {F : Type} [Field F] [NumberField F] {Δ : F} (a b : DA Δ) : a * b * a⁻¹ * b⁻¹ ∈ SA Δ := by
  refine Subgroup.mem_iInf.2 fun v => Subgroup.mem_comap.2 ?_
  rw [map_mul, map_mul, map_mul, map_inv, map_inv]
  exact comm_abs (GeneralLinearGroup.det.comp (DX (cv v Δ)).subtype) _ _

private lemma trz {A : Type} [Group A] (g : A) : LinearMap.trace ℂ PUnit ((1 : Representation ℂ A PUnit) g) = 0 := by
  rw [Subsingleton.elim ((1 : Representation ℂ A PUnit) g) 0, map_zero]

section
variable {F : Type} [Field F] [NumberField F] {Δ : F} (D : Dat Δ)

private lemma delta_ne (ok : D.Ok) : Δ ≠ 0 := by
  intro h0
  have w : NumberField.InfinitePlace F := Classical.arbitrary _
  have σ : F →+* ℝ := NumberField.InfinitePlace.embedding_of_isReal (ok.real.isReal w)
  have := ok.neg σ
  rw [h0, map_zero] at this
  exact lt_irrefl _ this

private lemma conK (bK : BaseK) (fK : FinK) (ok : D.Ok) (ι : DX Δ →* DA Δ) (hι : IsIotaD ι) :
    ZD Δ ≤ Subgroup.center (DX Δ) ∧ (∀ z ∈ ZD Δ, ι z ∈ Subgroup.center (DA Δ) ∧ ι z ∈ D.UZ) ∧
    (∃ T : Finset (DA Δ), ∀ g, ∃ γ, ∃ s ∈ T, ∃ u ∈ D.UZ, g = ι γ * s * u) ∧
    ∀ g, (ZD Δ).relIndex ((D.UZ.map (MulAut.conj g).toMonoidHom).comap ι) ≠ 0 := by
  obtain ⟨B, hB, -⟩ := bK F Δ D ok PUnit 1 0 (fun _ _ _ _ => Subsingleton.elim _ _) (fun g _ _ _ => trz g)
  have hF := (fK F Δ D ok PUnit 0 B hB).1
  have hBι : B.ι = ι := by
    ext γ : 1
    apply Subtype.ext
    funext v
    apply dx_ext
    rw [hB.ι γ v, hι γ v]
  have hU := hB.U
  have hΓ := hB.Γ₀
  refine ⟨?_, fun z hz => ?_, ?_, fun g => ?_⟩
  · have := B.cenΓ
    rwa [hΓ] at this
  · rw [← hΓ] at hz
    have h1 := B.cenG z hz
    have h2 := B.memU z hz
    rw [hBι] at h1 h2
    rw [hU] at h2
    exact ⟨h1, h2⟩
  · obtain ⟨T, hT⟩ := hF.cls
    refine ⟨T, fun g => ?_⟩
    have := hT g
    rwa [hU, hBι] at this
  · have := hF.stab g
    rwa [hU, hBι, hΓ] at this

private lemma bι {V : Type} [AddCommGroup V] [Module ℂ V] (ι : DX Δ →* DA Δ) (hι : IsIotaD ι) (ch : F → ℂ) (x : DA Δ)
    (B : Base (SU Δ) (SA Δ) V) (hB : D.IsBS ch x B) (γ : SU Δ) : ((B.ι γ : SA Δ) : DA Δ) = ι γ := by
  refine Subtype.ext (funext fun v => dx_ext ?_)
  rw [hB.ι, hι]

private lemma baseP (bS : BaseS) (ok : D.Ok) (x : DA Δ) : ∃ B : Base (SU Δ) (SA Δ) PUnit, D.IsBS 0 x B := by
  obtain ⟨B, hB, -⟩ := bS F Δ D ok PUnit 1 0 (fun γ _ _ => trz γ) x
  exact ⟨B, hB⟩

private lemma conS (bS : BaseS) (fS : FinS) (ok : D.Ok) (ι : DX Δ →* DA Δ) (hι : IsIotaD ι) :
    ∃ ι₁ : SU Δ →* SA Δ, (∀ γ, ((ι₁ γ : SA Δ) : DA Δ) = ι (γ : DX Δ)) ∧
    (∀ x : DA Δ, ∃ T : Finset (SA Δ), ∀ s, ∃ h, ∃ t ∈ T, ∃ u : SA Δ, x⁻¹ * u * x ∈ D.U2 ∧ s = ι₁ h * t * u) ∧
    ∀ x : DA Δ, {h : SU Δ | x⁻¹ * (ι₁ h : DA Δ) * x ∈ D.U2}.Finite := by
  obtain ⟨B0, hB0⟩ := baseP D bS ok 1
  have hι' : ∀ (x : DA Δ) (B : Base (SU Δ) (SA Δ) PUnit), D.IsBS 0 x B → B.ι = B0.ι := fun x B hB => by
    ext h : 1
    apply Subtype.ext
    rw [bι D ι hι 0 x B hB h, bι D ι hι 0 1 B0 hB0 h]
  refine ⟨B0.ι, fun γ => bι D ι hι 0 1 B0 hB0 γ, fun x => ?_, fun x => ?_⟩
  · obtain ⟨B, hB⟩ := baseP D bS ok x
    obtain ⟨T, hT⟩ := (fS F Δ D ok PUnit 0 x B hB).1.cls
    refine ⟨T, fun s => ?_⟩
    obtain ⟨h, t, ht, u, hu, rfl⟩ := hT s
    exact ⟨h, t, ht, u, (hB.U u).mp hu, by rw [hι' x B hB]⟩
  · obtain ⟨B, hB⟩ := baseP D bS ok x
    have hfin := (fS F Δ D ok PUnit 0 x B hB).1.stab 1
    rw [hB.Γ₀, Subgroup.relIndex_bot_left] at hfin
    have hK := Nat.finite_of_card_ne_zero hfin
    refine (Set.finite_coe_iff.mp hK).subset ?_
    intro h hh
    have hm : B.ι h ∈ B.U := by
      rw [hB.U, hι' x B hB]
      exact hh
    have he : (MulAut.conj (1 : SA Δ)).toMonoidHom (B.ι h) = B.ι h := by
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, one_mul, inv_one, mul_one]
    exact ⟨B.ι h, hm, he⟩

private lemma conN : (SA Δ).Normal := by
  unfold SA
  exact Subgroup.normal_iInf_normal fun v => Subgroup.Normal.comap (by unfold SU; infer_instance) _

private lemma conF (hSF : SuppFin) (bS : BaseS) (fS : FinS) (ok : D.Ok) (ι : DX Δ →* DA Δ) (hι : IsIotaD ι) (t : Dat.Par F)
    (ht : D.Cone t) (g : DA Δ) : {γ : SU Δ | D.FS t (g⁻¹ * ι γ * g) ≠ 0}.Finite := by
  obtain ⟨B, hB⟩ := baseP D bS ok g
  have h1 := fS F Δ D ok PUnit 0 g B hB
  have h2 := hSF _ _ _ B h1.1 hB.Γ₀ _ (h1.2 t ht) 1
  refine h2.subset ?_
  intro γ hγ
  simp only [Set.mem_setOf_eq, Dat.FSx, inv_one, mul_one, one_mul]
  rw [bι D ι hι 0 g B hB γ]
  exact hγ

private lemma clEx (hH : HasTrLaw) (ch : F → ℂ) : ∃ cl : DX Δ → ℂ, (∀ g s, HasTr g s → cl g = ch s) ∧ (∀ g, cl g ≠ 0 → g ∈ SU Δ) ∧
    ∀ h g, cl (h * g * h⁻¹) = cl g := by
  classical
  let cl : DX Δ → ℂ := fun g => if h : ∃ s, HasTr g s then ch h.choose else 0
  have key : ∀ g s, HasTr g s → cl g = ch s := by
    intro g s hs
    have he : ∃ s, HasTr g s := ⟨s, hs⟩
    show (if h : ∃ s, HasTr g s then ch h.choose else 0) = ch s
    rw [dif_pos he, (hH F Δ g).2.1 _ _ he.choose_spec hs]
  have zero : ∀ g, ¬ (∃ s, HasTr g s) → cl g = 0 := fun g he => dif_neg he
  refine ⟨cl, key, ?_, ?_⟩
  · intro g hg
    by_contra hn
    exact hg (zero g (fun he => hn ((hH F Δ g).1.mpr he)))
  · intro h g
    by_cases he : ∃ s, HasTr g s
    · obtain ⟨s, hs⟩ := he
      rw [key g s hs, key _ s (((hH F Δ g).2.2 h s).mpr hs)]
    · rw [zero g he, zero]
      rintro ⟨s, hs⟩
      exact he ⟨s, ((hH F Δ g).2.2 h s).mp hs⟩

end

set_option maxHeartbeats 3000000 in
private theorem fibre_of (hM : Master) (hTr : TrKer) (hSF : SuppFin) (hPair : Pair) (hReps : Reps) (hLev : LevFin) (hC : FSConj)
    (hSu : FSSupp) (hH : HasTrLaw) (bS : BaseS) (bK : BaseK) (fS : FinS) (fK : FinK) (cR : ClassRep) (eA : EmbAlg) : Fibre := by
  intro F _ _ Δ D ok ι hι x₀ hx₀
  have hΔ := delta_ne D ok
  obtain ⟨hU, hr⟩ := hLev F Δ D ok
  obtain ⟨hZ, hZt, hcls, hstab⟩ := conK D bK fK ok ι hι
  obtain ⟨ι₁, hι₁, hSc, hSf⟩ := conS D bS fS ok ι hι
  have hN1 : (SU Δ).Normal := MonoidHom.normal_ker _
  obtain ⟨c, hc, hall⟩ := glue hM hTr hPair ι (SA Δ) D.U2 D.UZ (SU Δ) (ZD Δ) ι₁ hι₁ comm_mem hN1 hZ hZt hU hr hSc hSf hcls hstab
  obtain ⟨Y, hY, hYc⟩ := cR F Δ D ok ι hι
  obtain ⟨n, x, hx0, hxY, hsep, hcov⟩ := hReps (DX Δ) (DA Δ) ι (SA Δ) D.UZ Y x₀ conN (fun g => by
    obtain ⟨γ, s, hs, y, hy, u, hu, e⟩ := hYc g
    exact ⟨γ, s, hs, y, hy, u, hU hu, e⟩)
  refine ⟨n, x, c, hx0, fun i => ?_, hc, ?_⟩
  · rcases hxY i with h | h
    · rw [h]; exact hx₀
    · exact hY _ h
  intro V _ _ _ ch B hB t ht I τ γ j hinj hi hcv
  obtain ⟨cl, hcl, hcl0, hclc⟩ := clEx hH ch
  have hE := fun i => eA F Δ (τ i) hΔ (hi i).1 (γ i) (hi i).2.1
  have key := hall n x hsep hcov V (D.FS t) B cl I γ (fun i => (Etau F (τ i))ˣ) j
    (fun u hu g => hC F Δ D ok t ht u hu g) (fun g => conF D hSF bS fS ok ι hι t ht g)
    (fun i => by
      ext1 γ'
      exact Subtype.ext ((bι D ι hι ch (x i) (B i) (hB i) γ').trans (hι₁ γ').symm))
    (fun i => (hB i).U) (fun i => (hB i).ω) (fun i => (hB i).Γ₀) (fun i => (fS F Δ D ok V ch (x i) (B i) (hB i)).1)
    (fun i => (fS F Δ D ok V ch (x i) (B i) (hB i)).2 t ht) hclc hcl0
    (fun i γ' => by
      obtain ⟨s, hs⟩ := (hH F Δ γ').1.1 γ'.2
      rw [(hB i).tr γ' s hs, hcl _ s hs])
    (fun i y => ((hE i).2.1 (j i) (hi i).2.2).2.1 y)
    (fun i i' h e => by
      have h1 : HasTr (γ i) (τ i') := ((hH F Δ (γ i)).2.2 h _).1 (e ▸ (hi i').2.1)
      exact hinj ((hH F Δ (γ i)).2.1 _ _ (hi i).2.1 h1))
    (fun γ' g hne => by
      obtain ⟨s, hs⟩ := (hH F Δ γ').1.1 (hcl0 γ' (left_ne_zero_of_mul hne))
      obtain ⟨i, rfl⟩ := hcv γ' s hs (hSu F Δ D ok ι hι t ht γ' s g hs (right_ne_zero_of_mul hne))
      obtain ⟨y, hy⟩ := (hE i).2.2 γ' hs
      exact ⟨i, y⁻¹, by rw [hy, inv_inv]⟩)
  refine key.trans (congrArg _ (finsum_congr fun i => ?_))
  rw [hcl _ _ (hi i).2.1, ((hE i).2.1 (j i) (hi i).2.2).2.2]

end UpperTheory.V.Z.Sym.Glob

theorem UpperTheory.V.Z.Sym.Glob.fibre :
    UpperTheory.V.Z.Sym.Glob.Fibre :=
  UpperTheory.V.Z.Sym.Glob.fibre_of UpperTheory.symmetric_fiber_master_formula UpperTheory.symmetric_fiber_trace_kernel UpperTheory.orbitalFiber_support_finite UpperTheory.orbitalFiber_pair_correspondence UpperTheory.orbitalFiber_representatives
    UpperTheory.orbitalFiber_level_finite UpperTheory.orbitalFiber_fixedSet_conj UpperTheory.orbitalFiber_fixedSet_support UpperTheory.orbitalFiber_hasTraceLaw UpperTheory.V.Z.Sym.Glob.baseS UpperTheory.V.Z.Sym.Glob.baseK
    UpperTheory.V.Z.Sym.Glob.finS UpperTheory.V.Z.Sym.Glob.finK UpperTheory.V.Z.Sym.Glob.classRep UpperTheory.V.Z.Sym.Glob.embAlg
