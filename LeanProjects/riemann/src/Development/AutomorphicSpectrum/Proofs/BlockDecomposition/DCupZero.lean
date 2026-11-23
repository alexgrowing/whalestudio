import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.HodgeSurjectivity.FormUniq
import Development.WeilBound.CoreStatements.PadicHodgeComparison.HodgeSurjectivity.NLeA
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.Imports
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.ChartGrConst
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FormConsMul
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LamFamily
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AppendCons
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AffineFinsetInf
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CupMemRelS

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedVariables false

open CategoryTheory Limits AlgebraicGeometry GlobalTheory.LogCris CrystallineSemistableComparison CrystallineSemistableComparison.Pb CrystallineSemistableComparison.HT CrystallineSemistableComparison.Onto

noncomputable section

namespace GlobalTheory.CompanionTheory.RelKill

theorem d_cup_zero {R : Type} [CommRing R] {C : Type 1} [Category.{0} C] {F₁ F₂ F₃ : C ⥤ ModuleCat.{0} R} (P : CH.Pairing F₁ F₂ F₃)
    {p n m : ℕ} {r : CH.Cn F₁ p} {z : CH.Cn F₂ n} (hr : CH.d F₁ p r = 0) (hz : CH.d F₂ n z = 0) (h : p + n = m) :
    CH.d F₃ m (P.cupC h r z) = 0 := by
  rw [CrystallineSemistableComparison.P.leibniz, hr, hz]
  simp

section Over
variable {K : Type} [Field K] [CharZero K] {W Y : Scheme.{0}} {q : Y ⟶ Spec (CommRingCat.of K)} {i : W ⟶ Y}
open GlobalTheory.CompanionTheory.RelInjAbs GlobalTheory.CompanionTheory.RelInjZ

set_option maxHeartbeats 2000000 in
theorem kill_over [IsSeparated q] [IsClosedImmersion i] (hTop : TopRes) (hFU : FormUniq) (hOR : OmRes) (hSL : SiteLaws) (hCD : CovDesc) (hZR : ZarRel)
    (hAO : AffOm) (hAR : AffRel) (hFL : FormLaws) (hDW : DWedge) (hDL : DLog) (hFC : FormCup) (hC1 : FirstChernCoboundary) (hCK : ConeKill)
    (D : E.LineData Y) (hQ : Cosieve (On q i))
    (bf : ∀ {V : Scheme.{0}} (a : V ⟶ D.Y), Γ(V, ⊤))
    (bf_nat : ∀ {V' V : Scheme.{0}} (g : V' ⟶ V) (a : V ⟶ D.Y), bf (g ≫ a) = g.appTop.hom (bf a))
    (bf_u : ∀ {V : Scheme.{0}} (a b : V ⟶ D.Y) (h : a ≫ D.f = b ≫ D.f), bf a = (D.u a b h : Γ(V, ⊤)) * bf b)
    {m : ℕ} (U : Fin m → Y.Opens) (σ : ∀ α, (U α : Scheme.{0}) ⟶ D.Y) (hσ : ∀ α, σ α ≫ D.f = (U α).ι)
    (hU : (⨆ α, U α) = ⊤) (haff : ∀ α α', IsAffineOpen (U α ⊓ U α'))
    (hcov : ∀ α (V : Y.Opens) (h : V ≤ U α), IsAffineOpen V →
      (∃ n, Nonempty (Coord q V n)) ∧ (∃ n, Nonempty (Coord (i ≫ q) (i ⁻¹ᵁ V) n)) ∧
      RingHom.ker (i.app V).hom = Ideal.span {V.topIso.hom.hom (bf (Y.homOfLE h ≫ σ α))} ∧
      ∀ (a : ℕ) (ω : Om K (Sec q V) a), (show Sec q V from V.topIso.hom.hom (bf (Y.homOfLE h ≫ σ α))) • ω = 0 → ω = 0)
    (r : CH.Cn (G q 1) 2) (hr : CH.d (G q 1) 2 r = 0) (hc1 : IsDlogFirstChernClass q D (clsH (a := 1) q r hr))
    (a n : ℕ) (z : CH.Cn (G q a) n) (hz : CH.d (G q a) n z = 0) (hzr : z ∈ relS (G q a) (On q i) n) :
    RelNull (G q (a + 1)) (On q i) (n + 2)
      (cupC q (a := 1) (a' := a) (Nat.add_comm 1 a) (Nat.add_comm 2 n) r z) := by
  classical
  obtain ⟨hc, -, htop, -, -, -⟩ := hSL K W Y Y q i (𝟙 Y)
  obtain ⟨ε, β, hβ, hβu⟩ := hC1 K Y q D (Fin m) U σ hσ r hr hc1
  let Uc : Fin m → ObjectProperty (Thick (smFun Y q)) := fun α => inU q (U α)
  let Vs : Finset (Fin m) → Y.Opens := fun S => S.inf U
  have hVle : ∀ {α : Fin m} {S : Finset (Fin m)}, α ∈ S → Vs S ≤ U α := fun h => Finset.inf_le h
  have hVT : ∀ {S T : Finset (Fin m)}, S ⊆ T → Vs T ≤ Vs S := fun h => Finset.inf_mono h
  have hVaff : ∀ S : Finset (Fin m), S.Nonempty → IsAffineOpen (Vs S) := fun S hS =>
    affine_finset_inf q U S hS fun o _ => by simpa using haff o o
  have hP : ∀ S : Finset (Fin m), S.Nonempty → capU Uc S = inU q (Vs S) := fun S hS =>
    capU_nonempty _ _ S hS fun T => inU_finset_inf hSL i U S T
  have hk : ∀ {S T : Finset (Fin m)}, S ⊆ T → inU q (Vs T) ≤ inU q (Vs S) := fun h T' hT =>
    (inU_finset_inf hSL i U _ T').2 fun o ho => (inU_finset_inf hSL i U _ T').1 hT o (h ho)
  have hd₁ : ∀ S : Finset (Fin m), S.Nonempty → ∃ d, Nonempty (Coord q (Vs S) d) := fun S ⟨α, hα⟩ =>
    (hcov α (Vs S) (hVle hα) (hVaff S ⟨α, hα⟩)).1
  have hd₂ : ∀ S : Finset (Fin m), S.Nonempty → ∃ d, Nonempty (Coord (i ≫ q) (i ⁻¹ᵁ Vs S) d) := fun S ⟨α, hα⟩ =>
    (hcov α (Vs S) (hVle hα) (hVaff S ⟨α, hα⟩)).2.1
  choose dd hdd using hd₁
  choose dd' hdd' using hd₂
  have hE : ∀ (S : Finset (Fin m)) (hS : S.Nonempty) (b : ℕ),
      ∃ e : Om K (Sec q (Vs S)) b →ₗ[K] HV q (Vs S) b b, IsOm q (Vs S) b e ∧ Function.Bijective e := fun S hS b =>
    (hAO K Y q (Vs S) (dd S hS) (hdd S hS) b).2
  choose E hEom hEb using hE
  have hOm := fun (S T : Finset (Fin m)) (h : S ⊆ T) => hOR K Y q (Vs S) (Vs T) (hVT h) (hk h)
  choose φ hφ1 hφ2 hφ3 using hOm
  let P := (grOk (smFun Y q) (Nat.add_comm 1 a)).pair
  have hUc : ∀ α, Cosieve (Uc α) := fun α => hc _
  have h1 : (covSy (G q a) Uc hQ).One a := fun S hS j hj =>
    one_P hAR hQ (hP S hS) (hdd S hS) (hdd' S hS) a j hj
  have h2 : (covSy (G q (a + 1)) Uc hQ).One (a + 1) := fun S hS j hj =>
    one_P hAR hQ (hP S hS) (hdd S hS) (hdd' S hS) (a + 1) j hj
  let e₂ : ∀ S : Finset (Fin m), S.Nonempty → (Om K (Sec q (Vs S)) a →ₗ[K] HU (G q a) (capU Uc S) a) := fun S hS =>
    (castH (G q a) (hP S hS) a).toLinearMap ∘ₗ E S hS a
  let e₃ : ∀ S : Finset (Fin m), S.Nonempty → (Om K (Sec q (Vs S)) (a + 1) →ₗ[K] HU (G q (a + 1)) (capU Uc S) (a + 1)) :=
    fun S hS => (castH (G q (a + 1)) (hP S hS) (a + 1)).toLinearMap ∘ₗ E S hS (a + 1)
  let fS : ∀ (α : Fin m) (S : Finset (Fin m)), α ∈ S → Sec q (Vs S) := fun α S hα =>
    (Vs S).topIso.hom.hom (bf (Y.homOfLE (hVle hα) ≫ σ α))
  have pf : ∀ (α α' : Fin m) (S : Finset (Fin m)) (hα : α ∈ S) (hα' : α' ∈ S),
      (Y.homOfLE (hVle hα) ≫ σ α) ≫ D.f = (Y.homOfLE (hVle hα') ≫ σ α') ≫ D.f := fun α α' S hα hα' => by
    simp [hσ]
  let uS : ∀ (α α' : Fin m) (S : Finset (Fin m)), α ∈ S → α' ∈ S → (Sec q (Vs S))ˣ := fun α α' S hα hα' =>
    Units.map (M := Γ((Vs S : Scheme.{0}), ⊤)) (N := Sec q (Vs S)) ((Vs S).topIso.hom.hom : _ →+* Γ(Y, Vs S)).toMonoidHom
      (D.u (Y.homOfLE (hVle hα) ≫ σ α) (Y.homOfLE (hVle hα') ≫ σ α') (pf α α' S hα hα'))
  have hφf : ∀ (α : Fin m) {S T : Finset (Fin m)} (h : S ⊆ T) (hα : α ∈ S), φ S T h (fS α S hα) = fS α T (h hα) := by
    intro α S T h hα
    rw [hφ1]
    refine (rs_topIso (hVT h) _).trans ?_
    rw [← bf_nat, ← Category.assoc, Scheme.homOfLE_homOfLE]
  let kk : ∀ {S T : Finset (Fin m)}, S ⊆ T → capU Uc T ≤ capU Uc S := fun h _ hT => ⟨hT.1, fun α hα => hT.2 α (h hα)⟩
  have huf : ∀ α α' S hα hα', fS α S hα = uS α α' S hα hα' * fS α' S hα' := fun α α' S hα hα' =>
    (congrArg (Vs S).topIso.hom.hom (bf_u _ _ (pf α α' S hα hα'))).trans (map_mul _ _ _)
  have hcup : ∀ α α' S hα hα' (y : CH.Cn ((capU Uc S).ι ⋙ G q a) a) (hy : CH.d _ a y = 0) (ω : Om K (Sec q (Vs S)) a)
      (w : Om K (Sec q (Vs S)) a →ₗ[Sec q (Vs S)] Om K (Sec q (Vs S)) (a + 1)),
      (∀ g₀ (g : Fin a → Sec q (Vs S)), w (form K g₀ g) = form K g₀ (Fin.cons (uS α α' S hα hα' : Sec q (Vs S)) g)) →
      (CH.cx _).cls y hy = e₂ S ⟨α, hα⟩ ω → ∀ hz,
      (CH.cx ((capU Uc S).ι ⋙ G q (a + 1))).cls ((pairU P (capU Uc S)).cupC (Nat.add_comm 1 a)
        ((resU (G q 1) (capU_le Uc S hα)).pullC 1 (β α) - (resU (G q 1) (capU_le Uc S hα')).pullC 1 (β α')) y) hz =
        e₃ S ⟨α, hα⟩ ((ε : ℤ) • ((↑(uS α α' S hα hα')⁻¹ : Sec q (Vs S)) • w ω)) := by
    intro α α' S hα hα' y hy ω w hw hcls hz
    have := cup_P hFL hFU hFC (hP S ⟨α, hα⟩) (capU_le Uc S hα) (capU_le Uc S hα') (β α) (β α') (E S ⟨α, hα⟩ a)
      (E S ⟨α, hα⟩ (a + 1)) (hEom S _ a) (hEom S _ (a + 1)) ((ε : ℤ) • (↑(uS α α' S hα hα')⁻¹ : Sec q (Vs S)))
      (uS α α' S hα hα' : Sec q (Vs S))
      (fun k₁ k₂ => hβu α α' (Vs S) (hVle hα) (hVle hα') k₁ k₂ (uS α α' S hα hα') (by
        change (Vs S).topIso.inv.hom ((Vs S).topIso.hom.hom _) = _
        rw [← CommRingCat.comp_apply, Iso.hom_inv_id]
        rfl)) w hw y hy ω hcls hz
    rw [smul_assoc] at this
    exact this
  let x : ((covSy (G q a) Uc hQ).K ∅).X n :=
    ⟨(CH.Mor.restrict (G q a) (capU Uc ∅).ι).pullC n z, fun s hs => hzr _ hs⟩
  have hx : ((covSy (G q a) Uc hQ).K ∅).d n x = 0 := Subtype.ext (by
    change CH.d _ n ((CH.Mor.restrict (G q a) (capU Uc ∅).ι).pullC n z) = 0
    rw [CH.Mor.d_pullC, hz, map_zero])
  have hB := cov_kill hCK hCD hDW hDL hFL P Uc hUc hQ a h1 h2 r hr β hβ (fun S => Sec q (Vs S)) e₂ e₃
    (fun S hS => (castH (G q a) (hP S hS) a).bijective.comp (hEb S hS a))
    (fun S hS => inj_P hAR hQ (hP S hS) (hdd S hS) (hdd' S hS) (a + 1) (E S hS (a + 1)) (hEom S hS (a + 1)))
    (fun S => kerI q i (Vs S))
    (fun S hS ω => range_P hAR hQ (hP S hS) (hdd S hS) (hdd' S hS) a (E S hS a) (hEom S hS a) ω)
    (fun S hS ω => range_P hAR hQ (hP S hS) (hdd S hS) (hdd' S hS) (a + 1) (E S hS (a + 1)) (hEom S hS (a + 1)) ω)
    fS (fun α S hα => (hcov α (Vs S) (hVle hα) (hVaff S ⟨α, hα⟩)).2.2.1)
    (fun α S hα ω => (hcov α (Vs S) (hVle hα) (hVaff S ⟨α, hα⟩)).2.2.2 (a + 1) ω) (ε : ℤ)
    (fun {S T} h => φ S T h) hφf kk
    (fun {S T} h hS hT ω => pull_P (hP S hS) (hP T hT) (kk h) a (E S hS a) (E T hT a) (omMap (φ S T h) a)
      (fun k' ω => hφ3 S T h a _ _ (hEom S hS a) (hEom T hT a) ω) ω)
    (fun {S T} h hS hT ω => pull_P (hP S hS) (hP T hT) (kk h) (a + 1) (E S hS (a + 1)) (E T hT (a + 1))
      (omMap (φ S T h) (a + 1)) (fun k' ω => hφ3 S T h (a + 1) _ _ (hEom S hS (a + 1)) (hEom T hT (a + 1)) ω) ω)
    uS huf hcup n x hx
  have hZ := bij_res_of_eq (capU_empty Uc) hQ (fun _ _ => htop _) (fun _ _ => htop _) (n + 2)
    (hZR K W Y q i hQ (Fin m) ⊤ U hU (fun _ _ => htop _) (a + 1) (n + 2))
  have hd : CH.d (G q (a + 1)) (n + 2) (P.cupC (Nat.add_comm 2 n) r z) = 0 := d_cup_zero P hr hz _
  exact relNull_top hTop (G q (a + 1)) hQ (inU q ⊤) (capU Uc ∅) htop _ hZ (P.cupC (Nat.add_comm 2 n) r z) hd
    (cup_mem_relS P hQ _ r z hzr) _ rfl hB

end Over

end GlobalTheory.CompanionTheory.RelKill
