import Development.WeilBound.CoreStatements.VolumeEquality.BaseUnifVecA
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.FamilyPeriodRiemannLattice
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LatticeTangentVectorsAffineOpen
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsExcisionNbhdAway
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.LieModelOfIsLieBasis
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.DifferentiableOnOfTendstoLocallyUniformlyOn

noncomputable section

namespace SheetDecomposition

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp GlobalTheory.VerticalDeriv GlobalTheory.FibreDeriv

theorem vecHolPre {V V' : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] [NormedAddCommGroup V'] [NormedSpace ℂ V']
    {X : Scheme.{0}} {B : Set V} {C : Set V'} {y : V → (Sp ℂ ⟶ X)} {φ : V' → V} (h : IsHolTo B y)
    (hC : IsOpen C) (hφ : DifferentiableOn ℂ φ C) (hm : Set.MapsTo φ C B) : IsHolTo C (fun c => y (φ c)) := by
  intro U f
  have hs : {c ∈ C | ⊤ ≤ y (φ c) ⁻¹ᵁ U} = C ∩ φ ⁻¹' {b ∈ B | ⊤ ≤ y b ⁻¹ᵁ U} := by
    ext c
    exact ⟨fun hc => ⟨hc.1, hm hc.1, hc.2⟩, fun hc => ⟨hc.1, hc.2.2⟩⟩
  refine ⟨?_, ?_⟩
  · rw [hs]; exact hφ.continuousOn.isOpen_inter_preimage hC (h U f).1
  · exact (h U f).2.comp (hφ.mono fun c hc => hc.1) fun c hc => ⟨hm hc.1, hc.2⟩

theorem vecDetAn {n g : ℕ} {h : (Fin n → ℂ) → Matrix (Fin g) (Fin g) ℂ} {t₀ : Fin n → ℂ}
    (hh : ∀ a b, AnalyticAt ℂ (fun t => h t a b) t₀) : AnalyticAt ℂ (fun t => (h t).det) t₀ := by
  simp only [Matrix.det_apply']
  exact Finset.analyticAt_fun_sum _ fun σ _ => analyticAt_const.mul (Finset.analyticAt_fun_prod _ fun i _ => hh _ _)

theorem vecInvAn {n g : ℕ} {h : (Fin n → ℂ) → Matrix (Fin g) (Fin g) ℂ} {t₀ : Fin n → ℂ} {w : (Fin n → ℂ) → Fin g → ℂ}
    (hh : ∀ a b, AnalyticAt ℂ (fun t => h t a b) t₀) (h0 : (h t₀).det ≠ 0) (hw : AnalyticAt ℂ w t₀) :
    AnalyticAt ℂ (fun t => (h t)⁻¹ *ᵥ w t) t₀ := by
  have hi : ∀ a b, AnalyticAt ℂ (fun t => (h t)⁻¹ a b) t₀ := fun a b => by
    simp only [Matrix.inv_def, Ring.inverse_eq_inv', Matrix.smul_apply, smul_eq_mul, Matrix.adjugate_apply]
    refine ((vecDetAn hh).inv h0).mul (vecDetAn fun a' b' => ?_)
    by_cases e : a' = b
    · subst e
      simpa only [Matrix.updateRow_self] using analyticAt_const
    · simpa only [Matrix.updateRow_ne e] using hh a' b'
  refine analyticAt_pi_iff.2 fun a => ?_
  simp only [Matrix.mulVec, dotProduct]
  exact Finset.analyticAt_fun_sum _ fun b _ => (hi a b).mul (analyticAt_pi_iff.1 hw b)

theorem goodExp_univ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Tor.Level H}
    {Xo : Moduli D l} {σ : KA l →+* ℂ} {g : ℕ} {ty : Fin g → (E →+* ℂ)} (FU : FamilyUnif Xo σ ty) (i : Fin FU.n)
    (R : RiemLat E g (FU.Di i).La) (P : (FU.Di i).La →+ (Fin g → ℂ)) (h : Matrix (Fin g) (Fin g) ℂ)
    (hP : IsPeriod (FU.Di i) ty P) (hR : R.form = (FU.Di i).EF) (hd : IsUnit h.det) (hPh : ∀ x, P x = h *ᵥ R.P x)
    (hol : IsHolTo Set.univ fun ζ => (FU.ex i P ζ).left) :
    GoodExp Xo.univ.t (FU.u i P) R (fun x => h *ᵥ x) fun ζ => (FU.ex i P ζ).left := by
  have hv : ∀ ζ, (FU.ex i P ζ).left ≫ Xo.univ.t.G.hom = FU.u i P := fun ζ => Over.w _
  refine ⟨hol, hv, ?_, fun w₁ w₂ u h₁ h₂ => ?_, fun u hu h0 => ?_, fun A₀ x v hx => ?_⟩
  · exact congrArg (fun a => a.left) ((FU.ex_ker i P hP 0).2 (zero_mem _))
  · exact ((FU.ex_diff i P hP).2 (Over.homMk u (isDerivAt0_vertical _ _ hv h₁)) h₁.1).unique h₁ h₂
  · exact ((FU.ex_diff i P hP).2 (Over.homMk u hu) h0).exists
  · exact FibreAtPeriod.fibreLatVec_of_period E H D l Xo σ g ty FU i R P h hP hR hd hPh A₀ x v hx

theorem vecSlice {n g : ℕ} {V : Set (Fin n → ℂ)} {Z : Scheme.{0}} {e : (Fin n → ℂ) → (Fin g → ℂ) → (Sp ℂ ⟶ Z)}
    (he : IsHolTo (V ×ˢ Set.univ) (fun bz : (Fin n → ℂ) × (Fin g → ℂ) => e bz.1 bz.2)) {t : Fin n → ℂ} (ht : t ∈ V) :
    IsHolTo Set.univ (e t) := by
  have k := vecHolPre (C := Set.univ) (φ := fun ζ : Fin g → ℂ => (t, ζ)) he isOpen_univ
    ((differentiable_const t).prodMk differentiable_id).differentiableOn fun ζ _ => ⟨ht, trivial⟩
  exact k

theorem vecMono {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] {X : Scheme.{0}} {B C : Set V} {y : V → (Sp ℂ ⟶ X)}
    (h : IsHolTo B y) (hC : IsOpen C) (hm : C ⊆ B) : IsHolTo C y := by
  have k := vecHolPre (φ := id) h hC differentiableOn_id hm
  exact k

theorem liftFam {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {X X' : Scheme.{0}} {t : SAB H X}
    {t' : SAB H X'} {f : X' ⟶ X} {n g : ℕ} {Λ : Type} [AddCommGroup Λ] [Module (𝓞 E) Λ] (m : SABMap t' t f)
    {V : Set (Fin n → ℂ)} (hV : IsOpen V) {t₀ : Fin n → ℂ} (ht₀ : t₀ ∈ V) {R : (Fin n → ℂ) → RiemLat E g Λ}
    {h : (Fin n → ℂ) → (Fin g → ℂ) → Fin g → ℂ} {z : (Fin n → ℂ) → (Sp ℂ ⟶ X')} {z₀ : (Fin n → ℂ) → (Sp ℂ ⟶ X)}
    (hz : IsHolTo V z) (hf : ∀ b ∈ V, z b ≫ f = z₀ b) {e : (Fin n → ℂ) → (Fin g → ℂ) → (Sp ℂ ⟶ t.G.left)}
    (he : IsHolTo (V ×ˢ Set.univ) (fun bz : (Fin n → ℂ) × (Fin g → ℂ) => e bz.1 bz.2))
    (G : ∀ b ∈ V, GoodExp t (z₀ b) (R b) (h b) (e b)) :
    ∃ e' : (Fin n → ℂ) → (Fin g → ℂ) → (Sp ℂ ⟶ t'.G.left),
      IsHolTo (V ×ˢ Set.univ) (fun bz : (Fin n → ℂ) × (Fin g → ℂ) => e' bz.1 bz.2) ∧
      ∀ b ∈ V, GoodExp t' (z b) (R b) (h b) (e' b) := by
  classical
  have p := m.cart.1
  have ex : ∀ b ∈ V, ∀ ζ, ∃ e' : Sp ℂ ⟶ t'.G.left, e' ≫ m.φ = e b ζ ∧ e' ≫ t'.G.hom = z b := fun b hb ζ =>
    ⟨p.lift (e b ζ) (z b) (((G b hb).vert ζ).trans (hf b hb).symm), p.lift_fst _ _ _, p.lift_snd _ _ _⟩
  haveI : Nonempty (Sp ℂ ⟶ t'.G.left) := ⟨(ex t₀ ht₀ 0).choose⟩
  choose! e' a₁ b₁ using ex
  have base : IsHolTo (V ×ˢ Set.univ) (fun bz : (Fin n → ℂ) × (Fin g → ℂ) => z bz.1) :=
    vecHolPre (φ := Prod.fst) hz (hV.prod isOpen_univ) (by fun_prop) fun b hb => hb.1
  have hE : IsHolTo (V ×ˢ Set.univ) (fun bz : (Fin n → ℂ) × (Fin g → ℂ) => e' bz.1 bz.2) :=
    GlobalTheory.HolTorsion.isHolTo_of_isPullback p (GlobalTheory.HolTorsion.isHolTo_congr he fun b hb => a₁ b.1 hb.1 b.2)
      (GlobalTheory.HolTorsion.isHolTo_congr base fun b hb => b₁ b.1 hb.1 b.2)
  exact ⟨e', hE, fun b hb => (G b hb).pull m (hf b hb) (vecSlice hE hb) (a₁ b hb) (b₁ b hb)⟩

theorem vecAt_of_goodExp (HC : HolCoord) {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H}
    {l : Tor.Level H} {Xo : Moduli D l} {c : Coeff l} {Y : Model Xo c (algebraMap (𝓞 c.F) c.F)} {S : Finset ℕ} {Ω : Type}
    [Field Ω] {K : Type} [Fintype K] {J : K → Type} {y : (Σ k, J k) → Ω} (𝔐 : HodgeCpt Y S y) {n g : ℕ} {Λ : Type}
    [AddCommGroup Λ] [Module (𝓞 E) Λ] {R : (Fin n → ℂ) → RiemLat E g Λ} {V : Set (Fin n → ℂ)}
    {z : (Fin n → ℂ) → (Sp ℂ ⟶ 𝔐.X)} {h : (Fin n → ℂ) → Matrix (Fin g) (Fin g) ℂ} (hV : IsOpen V) (hz : IsHolTo V z)
    (hh : ∀ a b, DifferentiableOn ℂ (fun t => h t a b) V) (hd : ∀ t ∈ V, IsUnit (h t).det)
    {e₂ : (Fin n → ℂ) → (Fin g → ℂ) → (Sp ℂ ⟶ 𝔐.t.G.left)}
    (hE₂ : IsHolTo (V ×ˢ Set.univ) (fun bz : (Fin n → ℂ) × (Fin g → ℂ) => e₂ bz.1 bz.2))
    (G₂ : ∀ t ∈ V, GoodExp 𝔐.t (z t) (R t) (fun x => h t *ᵥ x) (e₂ t)) {t₀ : Fin n → ℂ} (ht₀ : t₀ ∈ V) :
    VecAt 𝔐 R z t₀ := by
  intro m s hs
  classical

  have hsm : Smooth 𝔐.t.G.hom := 𝔐.t.semi.smooth
  obtain ⟨W, hW, v, hq, -, hval⟩ := HodgeMetric.FrameExt.exists_affine_frame 𝔐.X 𝔐.t.G Ω 𝔐.ξ 𝔐.Li 𝔐.M
    ⟨centre (z t₀), 𝔐.all _⟩ m s 𝔐.tie.gen fun a => ((𝔐.M.exists_valAt_iff _ _).1 (hs a)).2
  have hW0 : ⊤ ≤ z t₀ ⁻¹ᵁ W := fun x _ => by
    have : x = IsLocalRing.closedPoint ℂ := Subsingleton.elim _ _
    subst this
    exact hq
  let B : Set (Fin n → ℂ) := {b ∈ V | ⊤ ≤ z b ⁻¹ᵁ W}
  have hB : IsOpen B := (hz W 0).1
  have hB₀ : t₀ ∈ B := ⟨ht₀, hW0⟩
  let ψ : (Fin n → ℂ) → (Γ(𝔐.X, W) →+* ℂ) := fun t =>
    if k : ⊤ ≤ z t ⁻¹ᵁ W then Flat.BdryModel.evalHom _ W k else Flat.BdryModel.evalHom _ W hW0
  have hψ : ∀ a, DifferentiableOn ℂ (fun t => ψ t a) B := fun a => (hz W a).2.congr fun t ht => by
    simp only [ψ, valAt', dif_pos ht.2]
    rfl
  have hψz : ∀ t ∈ B, spMap (ψ t) ≫ hW.fromSpec = z t := fun t ht => by
    simp only [ψ, dif_pos ht.2]
    exact Flat.BdryModel.spMap_evalHom _ _ _ _
  have hco : ∀ a, ∀ t ∈ B, ∃ w, IsDerivAt0 (e₂ t) w (spMap (dualMap (ψ t)) ≫ (v a).left) := fun a t ht => by
    obtain ⟨u, hu, e⟩ := hval (ψ t) (z t) (hψz t ht) (𝔐.all _) a
    rw [← e]
    exact (G₂ t ht.1).onto u.left (Over.w u) (hu.isTanAt.trans (G₂ t ht.1).zero.symm)
  choose! w hw using hco
  have hwa : ∀ a, AnalyticAt ℂ (w a) t₀ := fun a =>
    HC _ n g B e₂ _ (v a).left ψ (w a) hB
      (vecMono hE₂ (hB.prod isOpen_univ) (Set.prod_mono (fun b hb => hb.1) subset_rfl)) hψ (hw a)
      (fun t ht => (G₂ t ht.1).uniq) t₀ hB₀
  refine ⟨fun a t => (h t)⁻¹ *ᵥ w a t, fun a => vecInvAn
    (fun a b => GlobalTheory.SCV.analyticAt_of_differentiableOn (hh a b) (hV.mem_nhds ht₀)) (hd t₀ ht₀).ne_zero (hwa a), ?_⟩
  filter_upwards [hB.mem_nhds hB₀] with t ht
  choose u hu e using hval (ψ t) (z t) (hψz t ht) (𝔐.all _)
  refine ⟨u, hu, (G₂ t ht.1).lat _ _ u fun a => ?_⟩
  rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ (hd t ht.1), Matrix.one_mulVec, e]
  exact hw a t ht

theorem vecOfPeriods_of : HolCoord → VecOfPeriods := by
  intro HC E _ _ _ H D l Xo c Y S Ω _ K _ J _ y 𝔐 κ σ g ty FU i n V z xF R P h hV hz hxF hP hh hall t₀ ht₀
  have hE₀ := (FU.hol i n V P hV hP).2
  have G₀ : ∀ t ∈ V, GoodExp Xo.univ.t (FU.u i (P t)) (R t) (fun x => h t *ᵥ x) fun ζ => (FU.ex i (P t) ζ).left :=
    fun t ht => goodExp_univ FU i (R t) (P t) (h t) (hP.1 t ht) (hall t ht).1 (hall t ht).2.1 (hall t ht).2.2.1
      (vecSlice (e := fun t ζ => (FU.ex i (P t) ζ).left) hE₀ ht)
  obtain ⟨e₁, hE₁, G₁⟩ := liftFam Y.m0.toSABMap hV ht₀ (z₀ := fun t => FU.u i (P t)) hxF
    (fun t ht => (hall t ht).2.2.2.2.1) (e := fun t ζ => (FU.ex i (P t) ζ).left) hE₀ G₀
  obtain ⟨e₂, hE₂, G₂⟩ := liftFam 𝔐.m hV ht₀ (z₀ := fun t => z t ≫ 𝔐.f) hz (fun _ _ => rfl)
    (e := fun t ζ => e₁ t ζ ≫ Y.m.φ) (GlobalTheory.HolTorsion.isHolTo_comp hE₁ Y.m.φ)
    (fun t ht => (G₁ t ht).push Y.m (hall t ht).2.2.2.1)
  exact vecAt_of_goodExp HC 𝔐 hV hz hh (fun t ht => (hall t ht).2.1) hE₂ G₂ ht₀

end SheetDecomposition
