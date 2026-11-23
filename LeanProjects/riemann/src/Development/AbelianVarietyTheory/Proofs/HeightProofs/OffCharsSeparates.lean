import Mathlib
import Development.AbelianVarietyTheory.Proofs.HeightProofs.ThetaContinuous

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.IndefiniteRowSideFullHecke
open scoped TensorProduct

namespace GlobalTheory.WeilTieCompare

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

variable {X : ThetaX D} {T : ThetaTied D X}

theorem split_iff (V W : HSp D) (χ χ' : X.Chr) : SplittingKernelQuotients.IsSplitting V W (T.eChr χ) (T.eChr χ') ↔
    ResEta D (T.eChr χ) V.rank ∧ ResEta D (T.eChr χ') W.rank := by
  have k : ∀ χ, IsHeckeChar D (T.eChr χ) := fun χ =>
    ((Set.ext_iff.1 T.eChr_range _).1 ⟨χ, rfl⟩).1
  exact ⟨fun h => ⟨h.resA, h.resB⟩, fun h => ⟨k χ, k χ', h.1, h.2⟩⟩

def Rel (C : SplittingKernelQuotients.Core T) (ev : ∀ V W, X.Sch V W →ₗ[ℂ] (WA V W → ℂ))
    (om : ∀ V W, X.Chr → X.Chr → (GA D V × GA D W →* Module.End ℂ (X.Sch V W))) : Prop :=
  ∀ (A B : HSp D) (hr : A.rank < B.rank),
    (∀ Φ, ev A B Φ ∘ kap A B = C.eUp A B hr.le Φ) ∧ (∀ Φ, ev B A Φ ∘ kapT A B = C.eDn A B hr Φ) ∧
    ∀ χA χB hs g h, om A B χA χB (g, h) = C.omUp A B hr.le χA χB hs (g, h) ∧
      om B A χB χA (h, g) = C.omDn A B hr χA χB hs (g, h)

def Match (Wl : WeilTied D X T) (C : SplittingKernelQuotients.Core T) : Prop := Wl.ψ = C.ψ ∧ Rel C Wl.evS Wl.om

def Twist (C : SplittingKernelQuotients.Core T) : Prop :=
  ∀ (A B : HSp D) (hr : A.rank < B.rank) χA χB χA' χB' hs hs' (g : GA D A) (h : GA D B), ∃ cg ch : Circle,
    HeisenbergWeilMatrices.IsTildeVal D (T.eChr χB' / T.eChr χB) (HeisenbergWeilMatrices.detA A g) cg ∧
    HeisenbergWeilMatrices.IsTildeVal D (T.eChr χA' / T.eChr χA) (HeisenbergWeilMatrices.detA B h) ch ∧
    C.om A B hr.le χA' χB' hs' (g, h) = ((cg⁻¹ * ch : Circle) : ℂ) • C.om A B hr.le χA χB hs (g, h)

def ExactModulus (Wl : WeilTied D X T) : Prop :=
  ∀ (A B : HSp D) χ χ', A.rank < B.rank → ResEta D (T.eChr χ) A.rank → ResEta D (T.eChr χ') B.rank →
    ∀ v e, HeisenbergWeilMatrices.IsSplitIdem D v e → ∀ g h, SuppAt e A g → SuppAt e B h → ∀ x y, IsDetAt e A g x → IsDetAt e B h y →
    ∀ ℓ : X.Sch A B →ₗ[ℂ] ℂ,
      (∀ u : WA A B, (∀ i j, cA D e * u i j = u i j) → ∀ Φ Φ',
        Wl.evS A B Φ' = Heisenberg₂ Wl.ψ A B u (Wl.evS A B Φ) → ℓ Φ' = ℓ Φ) →
      ∀ Φ, ℓ (Wl.om A B χ χ' (g, h) Φ) =
        (HeisenbergWeilMatrices.splitMod A B v e (g, h) : ℂ) * (splitFac A B (T.eChr χ) (T.eChr χ') x y : ℂ) * ℓ Φ

def Converges (Wl : WeilTied D X T) : Prop :=
  ∀ (V W : HSp D) χ χ', V.rank ≠ W.rank → ResEta D (T.eChr χ) V.rank → ResEta D (T.eChr χ') W.rank → V.SigOK →
    AllSome (fun m : Measure (GA D V) × Set (GA D V) => IsVolPair D V m.1 m.2) fun m =>
      ∀ (Φ : X.Sch V W) (F : X.cusp V) (h : GA D W),
        IntegrableOn (fun g => Wl.evS V W (Wl.om V W χ χ' (g, h) Φ) 0 * T.ev V (F : X.AF V) g) m.2 m.1

def EqualRank (T : ThetaTied D X) (ψ : AddChar (AF D.host.F) ℂ) : Prop :=
  ∀ A B : HSp D, A.rank = B.rank → ∃ E : X.Sch A B ≃ₗ[ℂ] HeisenbergWeilMatrices.Theta ψ A B,
    ∀ χA χB, SplittingKernelQuotients.IsSplitting A B (T.eChr χA) (T.eChr χB) → ∃ om : SplittingKernelQuotients.Rep ψ A B,
      HeisenbergWeilMatrices.IsWeil ψ (T.eChr χA) (T.eChr χB) om ∧ (A.SigOK → ∀ (Φ : X.Sch A B) (φ : X.cusp A) (h : GA D B),
        SplittingKernelQuotients.IsQuotInt A (T.petC A) (fun g => SplittingKernelQuotients.kern om (E Φ) g h * T.ev A (φ : X.AF A) g)
          (T.ev B (X.th A B χA χB Φ φ) h))

def EqualRankWith (T : ThetaTied D X) (ψ : AddChar (AF D.host.F) ℂ)
    (P : ∀ A B : HSp D, (X.Sch A B → WA A B → ℂ) → Prop) : Prop :=
  ∀ A B : HSp D, A.rank = B.rank → ∃ E : X.Sch A B ≃ₗ[ℂ] HeisenbergWeilMatrices.Theta ψ A B, (P A B fun Φ => (E Φ : WA A B → ℂ)) ∧
    ∀ χA χB, SplittingKernelQuotients.IsSplitting A B (T.eChr χA) (T.eChr χB) → ∃ om : SplittingKernelQuotients.Rep ψ A B,
      HeisenbergWeilMatrices.IsWeil ψ (T.eChr χA) (T.eChr χB) om ∧ (A.SigOK → ∀ (Φ : X.Sch A B) (φ : X.cusp A) (h : GA D B),
        SplittingKernelQuotients.IsQuotInt A (T.petC A) (fun g => SplittingKernelQuotients.kern om (E Φ) g h * T.ev A (φ : X.AF A) g)
          (T.ev B (X.th A B χA χB Φ φ) h))

def EqualRankPure (T : ThetaTied D X) (ψ : AddChar (AF D.host.F) ℂ) : Prop :=
  EqualRankWith T ψ fun A B ev => ∀ Φ, Φ ∈ X.fact A B ↔ SplittingKernelQuotients.IsPure ψ (ev Φ)

def FactPure (Wl : WeilTied D X T) : Prop :=
  ∀ A B : HSp D, A.rank < B.rank →
    (∀ Φ, Φ ∈ X.fact A B ↔ SplittingKernelQuotients.IsPure Wl.ψ (Wl.evS A B Φ ∘ kap A B)) ∧
    ∀ Φ, Φ ∈ X.fact B A ↔ SplittingKernelQuotients.IsPure Wl.ψ (Wl.evS B A Φ ∘ kapT A B)

section FromRel

variable {C : SplittingKernelQuotients.Core T} {ev : ∀ V W, X.Sch V W →ₗ[ℂ] (WA V W → ℂ)}
  {om : ∀ V W, X.Chr → X.Chr → (GA D V × GA D W →* Module.End ℂ (X.Sch V W))}

theorem Rel.up (R : Rel C ev om) {A B : HSp D} (hr : A.rank < B.rank) {χA χB} (hs) (g h) (Φ) :
    C.eUp A B hr.le (om A B χA χB (g, h) Φ) = C.om A B hr.le χA χB hs (g, h) (C.eUp A B hr.le Φ) := by
  rw [((R A B hr).2.2 χA χB hs g h).1]
  simp [SplittingKernelQuotients.Core.omUp, LinearEquiv.conj_apply]

theorem Rel.dn (R : Rel C ev om) {A B : HSp D} (hr : A.rank < B.rank) {χA χB} (hs) (g h) (Φ) :
    C.eDn A B hr (om B A χB χA (h, g) Φ) = C.om A B hr.le χA χB hs (g, h) (C.eDn A B hr Φ) := by
  rw [((R A B hr).2.2 χA χB hs g h).2]
  simp [SplittingKernelQuotients.Core.omDn, LinearEquiv.conj_apply]

theorem Rel.kernUp (R : Rel C ev om) {A B : HSp D} (hr : A.rank < B.rank) {χA χB} (hs) (g h) (Φ) :
    ev A B (om A B χA χB (g, h) Φ) 0 = SplittingKernelQuotients.kern (C.om A B hr.le χA χB hs) (C.eUp A B hr.le Φ) g h := by
  rw [ev_zero (R A B hr).1, R.up hr hs]; rfl

theorem Rel.kernDn (R : Rel C ev om) {A B : HSp D} (hr : A.rank < B.rank) {χA χB} (hs) (g h) (Φ) :
    ev B A (om B A χB χA (h, g) Φ) 0 = SplittingKernelQuotients.kern (C.om A B hr.le χA χB hs) (C.eDn A B hr Φ) g h := by
  rw [ev_zero (R A B hr).2.1, R.dn hr hs]; rfl

theorem Rel.transpose_iff (R : Rel C ev om) {A B : HSp D} (hr : A.rank < B.rank) (Φ : X.Sch A B) (Φ' : X.Sch B A) :
    (∀ x : WA A B, ev B A Φ' xᵀ = ev A B Φ x) ↔ C.eDn A B hr Φ' = C.eUp A B hr.le Φ := by
  rw [(kap A B).surjective.forall, Subtype.ext_iff, ← (R A B hr).1, ← (R A B hr).2.1, funext_iff]
  rfl

theorem Rel.transpose_iff' (R : Rel C ev om) {A B : HSp D} (hr : A.rank < B.rank) (Φ : X.Sch A B) (Φ' : X.Sch B A) :
    (∀ x : WA B A, ev A B Φ xᵀ = ev B A Φ' x) ↔ C.eDn A B hr Φ' = C.eUp A B hr.le Φ := by
  rw [← R.transpose_iff hr]
  exact ⟨fun h x => (h xᵀ).symm, fun h x => (h xᵀ).symm⟩

theorem Rel.smul (R : Rel C ev om) {A B : HSp D} (hr : A.rank < B.rank) {χA χB χA' χB' hs hs' g h} {c : ℂ}
    (H : C.om A B hr.le χA' χB' hs' (g, h) = c • C.om A B hr.le χA χB hs (g, h)) :
    om A B χA' χB' (g, h) = c • om A B χA χB (g, h) ∧ om B A χB' χA' (h, g) = c • om B A χB χA (h, g) := by
  constructor
  · refine LinearMap.ext fun Φ => (C.eUp A B hr.le).injective ?_
    rw [R.up hr hs', H, LinearMap.smul_apply, LinearMap.smul_apply, map_smul, R.up hr hs]
  · refine LinearMap.ext fun Φ => (C.eDn A B hr).injective ?_
    rw [R.dn hr hs', H, LinearMap.smul_apply, LinearMap.smul_apply, map_smul, R.dn hr hs]

theorem tilde_val {χ : (AE D)ˣ →* Circle} (h0 : ResEta D χ 0) (V : HSp D) (g : GA D V) {x : (AE D)ˣ}
    (hx : IsDetRoot V g x) : HeisenbergWeilMatrices.IsTildeVal D χ (HeisenbergWeilMatrices.detA V g) (χ x) := by
  refine ⟨⟨x, (isDetRoot_iff V g x).1 hx⟩, fun y hy => ?_⟩
  obtain ⟨a, rfl⟩ := (GlobalTheory.Member.isDetRoot_laws D V).2.1 g x y hx ((isDetRoot_iff V g y).2 hy)
  obtain ⟨η, hη⟩ := h0.1
  rw [map_mul, h0.2 η hη, pow_zero, mul_one]

theorem tilde_one {χ : (AE D)ˣ →* Circle} {u c} (h : HeisenbergWeilMatrices.IsTildeVal D (χ / χ) u c) : c = 1 := by
  obtain ⟨x, hx⟩ := h.1
  rw [← h.2 x hx, div_self', MonoidHom.one_apply]

theorem tilde_mul {χ ν : X.Chr} {V : HSp D} {g : GA D V} {x c} (hx : IsDetRoot V g x)
    (h : HeisenbergWeilMatrices.IsTildeVal D (T.eChr (χ * ν) / T.eChr χ) (HeisenbergWeilMatrices.detA V g) c) : c = T.eChr ν x := by
  rw [map_mul, mul_div_cancel_left] at h
  exact (h.2 x ((isDetRoot_iff V g x).1 hx)).symm

theorem Twist.target (H : Twist C) (A B : HSp D) (hr : A.rank < B.rank) (χA χB ν hs hs' g h x) (hx : IsDetRoot A g x) :
    C.om A B hr.le χA (χB * ν) hs' (g, h) = (((T.eChr ν x)⁻¹ : Circle) : ℂ) • C.om A B hr.le χA χB hs (g, h) := by
  obtain ⟨cg, ch, h1, h2, h3⟩ := H A B hr χA χB χA (χB * ν) hs hs' g h
  rwa [tilde_one h2, tilde_mul hx h1, mul_one] at h3

theorem Twist.source (H : Twist C) (A B : HSp D) (hr : A.rank < B.rank) (χA χB ν hs hs' g h x) (hx : IsDetRoot B h x) :
    C.om A B hr.le (χA * ν) χB hs' (g, h) = ((T.eChr ν x : Circle) : ℂ) • C.om A B hr.le χA χB hs (g, h) := by
  obtain ⟨cg, ch, h1, h2, h3⟩ := H A B hr χA χB (χA * ν) χB hs hs' g h
  rwa [tilde_one h1, tilde_mul hx h2, inv_one, one_mul] at h3

theorem Rel.twist (R : Rel C ev om) : TwRule T om → Twist C := by
  intro H A B hr χA χB χA' χB' hs hs' g h
  obtain ⟨x, hx⟩ := GlobalTheory.RecDict.exists_isDetRoot D A g
  obtain ⟨y, hy⟩ := GlobalTheory.RecDict.exists_isDetRoot D B h
  have z : ∀ {χ χ' : X.Chr} {n}, ResEta D (T.eChr χ) n → ResEta D (T.eChr χ') n → ResEta D (T.eChr (χ' / χ)) 0 :=
    fun {χ χ' n} h h' => by
      rw [div_eq_mul_inv, map_mul, map_inv]
      exact resEta_parity (resEta_mul h' (resEta_inv h)) (by omega)
  have hA := z hs.resA hs'.resA
  have hB := z hs.resB hs'.resB
  have e1 := H.twW_up A B χA' χB (χB' / χB) hr hs'.resA hs.resB hB g h x hx
  have e2 := H.twV_up A B χA χB (χA' / χA) hr hs.resA hs.resB hA g h y hy
  rw [mul_div_cancel] at e1 e2
  refine ⟨_, _, map_div T.eChr _ _ ▸ tilde_val hB A g hx, map_div T.eChr _ _ ▸ tilde_val hA B h hy, ?_⟩
  refine LinearMap.ext fun f => ?_
  obtain ⟨Φ, rfl⟩ := (C.eUp A B hr.le).surjective f
  rw [LinearMap.smul_apply, ← R.up hr hs, ← R.up hr hs', e1, e2, smul_smul, LinearMap.smul_apply, map_smul,
    Circle.coe_mul, map_div, map_div]

theorem Rel.twRule (R : Rel C ev om) (H : Twist C) : TwRule T om := by
  have m : ∀ {χ ν : X.Chr} {n}, ResEta D (T.eChr χ) n → ResEta D (T.eChr ν) 0 → ResEta D (T.eChr (χ * ν)) n :=
    fun h h' => by rw [map_mul]; exact resEta_mul h h'
  exact ⟨fun V W χ χ' ν hr h1 h2 h0 g h x hx => (R.smul hr (H.target V W hr χ χ' ν ((split_iff _ _ _ _).2 ⟨h1, h2⟩)
      ((split_iff _ _ _ _).2 ⟨h1, m h2 h0⟩) g h x hx)).1,
    fun V W χ χ' ν hr h1 h2 h0 g h x hx => (R.smul hr (H.source V W hr χ χ' ν ((split_iff _ _ _ _).2 ⟨h1, h2⟩)
      ((split_iff _ _ _ _).2 ⟨m h1 h0, h2⟩) g h x hx)).1,
    fun V W χ χ' ν hr h1 h2 h0 g h x hx => (R.smul hr (H.source W V hr χ' χ ν ((split_iff _ _ _ _).2 ⟨h2, h1⟩)
      ((split_iff _ _ _ _).2 ⟨m h2 h0, h1⟩) h g x hx)).2,
    fun V W χ χ' ν hr h1 h2 h0 g h x hx => (R.smul hr (H.target W V hr χ' χ ν ((split_iff _ _ _ _).2 ⟨h2, h1⟩)
      ((split_iff _ _ _ _).2 ⟨h2, m h1 h0⟩) h g x hx)).2⟩

theorem Rel.twRule_iff (R : Rel C ev om) : TwRule T om ↔ Twist C := ⟨R.twist, R.twRule⟩

end FromRel

theorem exists_equiv {A B V W : HSp D} {κ : WA A B ≃+ WA V W} {σ} (hκ : IsChange κ σ) {ψ : AddChar (AF D.host.F) ℂ}
    (hψ : Continuous ψ) {S : Type} [AddCommGroup S] [Module ℂ S] (ev : S →ₗ[ℂ] (WA V W → ℂ)) (hi : Function.Injective ev)
    (hr : Set.range ev = {f | IsThetaFun ψ V W f}) : ∃ E : S ≃ₗ[ℂ] HeisenbergWeilMatrices.Theta ψ A B, ∀ Φ, ev Φ ∘ κ = E Φ := by
  let L : S →ₗ[ℂ] HeisenbergWeilMatrices.Theta ψ A B := LinearMap.codRestrict _ (LinearMap.funLeft ℂ ℂ κ ∘ₗ ev) fun Φ =>
    (theta_iff hκ hψ _).1 ((Set.ext_iff.1 hr _).1 ⟨Φ, rfl⟩)
  refine ⟨LinearEquiv.ofBijective L ⟨fun Φ Φ' h => hi (κ.surjective.injective_comp_right (congrArg Subtype.val h)),
    fun f => ?_⟩, fun _ => rfl⟩
  have e : ((f : WA A B → ℂ) ∘ κ.symm) ∘ κ = f := funext fun x => congrArg (f : WA A B → ℂ) (κ.symm_apply_apply x)
  obtain ⟨Φ, hΦ⟩ := (Set.ext_iff.1 hr _).2 ((theta_iff hκ hψ _).2 (e.symm ▸ f.2))
  exact ⟨Φ, Subtype.ext ((congrArg (· ∘ κ) hΦ).trans e)⟩

theorem range_eq {A B V W : HSp D} {κ : WA A B ≃+ WA V W} {σ} (hκ : IsChange κ σ) {ψ : AddChar (AF D.host.F) ℂ}
    (hψ : Continuous ψ) {S : Type} [AddCommGroup S] [Module ℂ S] {ev : S →ₗ[ℂ] (WA V W → ℂ)}
    {E : S ≃ₗ[ℂ] HeisenbergWeilMatrices.Theta ψ A B} (hE : ∀ Φ, ev Φ ∘ κ = E Φ) : Set.range ev = {f | IsThetaFun ψ V W f} := by
  ext f
  rw [Set.mem_ofPred_eq, theta_iff hκ hψ]
  constructor
  · rintro ⟨Φ, rfl⟩
    rw [hE]; exact (E Φ).2
  · intro h
    obtain ⟨Φ, hΦ⟩ := E.surjective ⟨_, h⟩
    exact ⟨Φ, κ.surjective.injective_comp_right ((hE Φ).trans (congrArg Subtype.val hΦ))⟩

theorem scalar_eq {A B : HSp D} (hr : A.rank ≤ B.rank) (c c' : (AE D)ˣ →* Circle) {v e} (he : HeisenbergWeilMatrices.IsSplitIdem D v e)
    (g : GA D A) (h : GA D B) : HeisenbergWeilMatrices.splitScalar A B c c' he (g, h) = (HeisenbergWeilMatrices.splitMod A B v e (g, h) : ℂ) *
      (splitFac A B c c' (HeisenbergWeilMatrices.atIdem he.idem (HeisenbergWeilMatrices.detA A g)) (HeisenbergWeilMatrices.atIdem he.idem (HeisenbergWeilMatrices.detA B h)) : ℂ) := by
  unfold splitFac
  rw [if_pos hr, mul_comm]
  rfl

theorem exists_rel (C : SplittingKernelQuotients.Core T) : ∃ ev om, (∀ V W, Function.Injective (ev V W)) ∧ Rel C ev om := by
  classical
  have h1 : ∀ V W : HSp D, ∃ ev : X.Sch V W →ₗ[ℂ] (WA V W → ℂ), Function.Injective ev ∧
      (∀ hr : V.rank < W.rank, ∀ Φ, ev Φ ∘ kap V W = C.eUp V W hr.le Φ) ∧
      ∀ hr : W.rank < V.rank, ∀ Φ, ev Φ ∘ kapT W V = C.eDn W V hr Φ := by
    intro V W
    rcases le_or_gt V.rank W.rank with h | h
    · refine ⟨LinearMap.funLeft ℂ ℂ (kap V W).symm ∘ₗ (Submodule.subtype _) ∘ₗ (C.eUp V W h).toLinearMap,
        fun Φ Φ' e => (C.eUp V W h).injective (Subtype.ext ((kap V W).symm.surjective.injective_comp_right e)),
        fun _ Φ => funext fun x => congrArg (C.eUp V W h Φ : WA V W → ℂ) ((kap V W).symm_apply_apply x),
        fun hr => absurd h (not_le.2 hr)⟩
    · refine ⟨LinearMap.funLeft ℂ ℂ (kapT W V).symm ∘ₗ (Submodule.subtype _) ∘ₗ (C.eDn W V h).toLinearMap,
        fun Φ Φ' e => (C.eDn W V h).injective (Subtype.ext ((kapT W V).symm.surjective.injective_comp_right e)),
        fun hr => absurd h (not_lt.2 hr.le),
        fun _ Φ => funext fun x => congrArg (C.eDn W V h Φ : WA W V → ℂ) ((kapT W V).symm_apply_apply x)⟩
  have h2 : ∀ (V W : HSp D) (χ χ' : X.Chr), ∃ om : GA D V × GA D W →* Module.End ℂ (X.Sch V W),
      (∀ (hr : V.rank < W.rank) hs g h, om (g, h) = C.omUp V W hr.le χ χ' hs (g, h)) ∧
      ∀ (hr : W.rank < V.rank) hs g h, om (g, h) = C.omDn W V hr χ' χ hs (h, g) := by
    intro V W χ χ'
    by_cases hs : SplittingKernelQuotients.IsSplitting V W (T.eChr χ) (T.eChr χ')
    · rcases le_or_gt V.rank W.rank with h | h
      · exact ⟨(C.eUp V W h).symm.conjRingEquiv.toMonoidHom.comp (C.om V W h χ χ' hs), fun _ _ _ _ => rfl,
          fun hr => absurd h (not_le.2 hr)⟩
      · exact ⟨((C.eDn W V h).symm.conjRingEquiv.toMonoidHom.comp (C.om W V h.le χ' χ hs.symm)).comp
          MulEquiv.prodComm.toMonoidHom, fun hr => absurd h (not_lt.2 hr.le), fun _ _ _ _ => rfl⟩
    · exact ⟨1, fun _ h => absurd h hs, fun _ h => absurd h.symm hs⟩
  choose ev h11 h12 h13 using h1
  choose om h21 h22 using h2
  exact ⟨ev, om, h11, fun A B hr => ⟨h12 A B hr, h13 B A hr, fun χA χB hs g h =>
    ⟨h21 A B χA χB hr hs g h, h22 B A χB χA hr hs h g⟩⟩⟩

section Build

variable {C : SplittingKernelQuotients.Core T} {ev : ∀ V W, X.Sch V W →ₗ[ℂ] (WA V W → ℂ)}
  {om : ∀ V W, X.Chr → X.Chr → (GA D V × GA D W →* Module.End ℂ (X.Sch V W))}

theorem Rel.splitUp (R : Rel C ev om) {A B : HSp D} (hr : A.rank < B.rank) {χ χ'}
    (hs : SplittingKernelQuotients.IsSplitting A B (T.eChr χ) (T.eChr χ')) {v e} (he : HeisenbergWeilMatrices.IsSplitIdem D v e) {g h}
    (hg : SuppAt e A g) (hh : SuppAt e B h) {x y} (hx : IsDetAt e A g x) (hy : IsDetAt e B h y) :
    HeisenbergWeilMatrices.ActsBy e (C.om A B hr.le χ χ' hs (g, h))
      ((HeisenbergWeilMatrices.splitMod A B v e (g, h) : ℂ) * (splitFac A B (T.eChr χ) (T.eChr χ') x y : ℂ)) := by
  rw [(isDetAt_iff he.idem A g x).1 hx, (isDetAt_iff he.idem B h y).1 hy, ← scalar_eq hr.le]
  exact (C.om_weil A B hr.le χ χ' hs).split v e he (g, h) ((suppAt_iff he A g).1 hg) ((suppAt_iff he B h).1 hh)

def Rel.tied (R : Rel C ev om) (hi : ∀ V W, Function.Injective (ev V W)) (tw : Twist C) : WeilTied D X T where
  ψ := C.ψ
  ψ_std := (stdChar_iff _).2 C.ψ_std
  evS := ev
  evS_inj := hi
  evS_range V W hne := by
    rcases lt_or_gt_of_ne hne with hr | hr
    · exact range_eq (isChange_kap hr.le) C.ψ_std.1.1 (R V W hr).1
    · exact range_eq (isChange_kapT hr) C.ψ_std.1.1 (R W V hr).2.1
  om := om
  om_heis V W χ χ' hne h1 h2 g h := by
    have hs := (split_iff V W χ χ').2 ⟨h1, h2⟩
    rcases lt_or_gt_of_ne hne with hr | hr
    · exact (impl_iff (isChange_kap hr.le) (R V W hr).1 (R.up hr hs g h) g h).2 ((C.om_weil _ _ _ _ _ hs).impl _)
    · exact (impl_iff (isChange_kapT hr) (R W V hr).2.1 (R.dn hr hs.symm h g) g h).2
        ((C.om_weil _ _ _ _ _ hs.symm).impl _)
  om_aut V W χ χ' hne h1 h2 γ hγ γ' hγ' Φ := by
    have hs := (split_iff V W χ χ').2 ⟨h1, h2⟩
    rcases lt_or_gt_of_ne hne with hr | hr
    · rw [R.kernUp hr hs, ev_zero (R V W hr).1]
      exact (C.om_weil _ _ _ _ _ hs).rat γ hγ γ' hγ' _
    · rw [R.kernDn hr hs.symm, ev_zero (R W V hr).2.1]
      exact (C.om_weil _ _ _ _ _ hs.symm).rat γ' hγ' γ hγ _
  om_cont V W χ χ' hne h1 h2 Φ w := by
    have hs := (split_iff V W χ χ').2 ⟨h1, h2⟩
    rcases lt_or_gt_of_ne hne with hr | hr
    · obtain ⟨x, rfl⟩ := (kap V W).surjective w
      refine ((C.om_weil V W hr.le _ _ hs).cont (C.eUp V W hr.le Φ) x).congr fun p => ?_
      rw [← R.up hr hs p.1 p.2, ← (R V W hr).1]; rfl
    · obtain ⟨x, rfl⟩ := (kapT W V).surjective w
      refine (((C.om_weil W V hr.le _ _ hs.symm).cont (C.eDn W V hr Φ) x).comp continuous_swap).congr fun p => ?_
      have := congrFun ((R W V hr).2.1 (om V W χ χ' (p.1, p.2) Φ)) x
      rw [R.dn hr hs.symm p.2 p.1] at this
      exact this.symm
  om_unit V W χ χ' hne h1 h2 μ 𝓕 hμ hF p Φ := by
    have hs := (split_iff V W χ χ').2 ⟨h1, h2⟩
    rcases lt_or_gt_of_ne hne with hr | hr
    · refine (unit_iff (isChange_kap hr.le) (R V W hr).1 C.ψ_std.1 hr.le Φ (om V W χ χ' (p.1, p.2) Φ)).2 ?_ μ 𝓕 hμ hF
      rw [R.up hr hs]
      exact (C.om_weil _ _ _ _ _ hs).unitary _ _
    · refine (unit_iff (isChange_kapT hr) (R W V hr).2.1 C.ψ_std.1 hr.le Φ (om V W χ χ' (p.1, p.2) Φ)).2 ?_ μ 𝓕 hμ hF
      rw [R.dn hr hs.symm]
      exact (C.om_weil _ _ _ _ _ hs.symm).unitary _ _
  om_split V W χ χ' hne h1 h2 e he g h hg hh x y hx hy := by
    have hs := (split_iff V W χ χ').2 ⟨h1, h2⟩
    obtain ⟨v, he⟩ := (isSplitIdem_iff e).1 he
    rcases lt_or_gt_of_ne hne with hr | hr
    · exact ⟨_, splitMod_pos he V W (g, h), (actsBy_iff (isChange_kap hr.le) (R V W hr).1 (R.up hr hs g h) e _).2
        (R.splitUp hr hs he hg hh hx hy)⟩
    · refine ⟨_, splitMod_pos he W V (h, g), ?_⟩
      rw [← splitFac_swap V W hne]
      exact (actsBy_iff (isChange_kapT hr) (R W V hr).2.1 (R.dn hr hs.symm h g) e _).2
        (R.splitUp hr hs.symm he hh hg hy hx)
  om_tw := R.twRule_iff.2 tw
  om_swap V W χ χ' hne h1 h2 g h Φ Φ' H := by
    have hs := (split_iff V W χ χ').2 ⟨h1, h2⟩
    rcases lt_or_gt_of_ne hne with hr | hr
    · rw [R.transpose_iff hr] at H ⊢
      rw [R.up hr hs, R.dn hr hs, H]
    · rw [R.transpose_iff' hr] at H ⊢
      rw [R.up hr hs.symm, R.dn hr hs.symm, H]
  th V W χ χ' hne h1 h2 hsig μ 𝓕 hv Φ F h := by
    have hs := (split_iff V W χ χ').2 ⟨h1, h2⟩
    rcases lt_or_gt_of_ne hne with hr | hr
    · simp only [R.kernUp hr hs]
      exact ((C.thUp V W hr.le χ χ' hs hsig Φ F h).2 (μ, 𝓕) hv).2
    · simp only [R.kernDn hr hs.symm]
      exact ((C.thDn W V hr χ' χ hs.symm hsig Φ F h).2 (μ, 𝓕) hv).2

end Build

theorem exists_tied (C : SplittingKernelQuotients.Core T) (tw : Twist C) : ∃ Wl : WeilTied D X T, Match Wl C := by
  obtain ⟨ev, om, hi, R⟩ := exists_rel C
  exact ⟨R.tied hi tw, rfl, R⟩

theorem isWeil_of_tied (Wl : WeilTied D X T) (hm : ExactModulus Wl) {A B : HSp D} (hr : A.rank < B.rank) {χA χB}
    (hs : SplittingKernelQuotients.IsSplitting A B (T.eChr χA) (T.eChr χB)) {E : X.Sch A B ≃ₗ[ℂ] HeisenbergWeilMatrices.Theta Wl.ψ A B}
    (hE : ∀ Φ, Wl.evS A B Φ ∘ kap A B = E Φ) {N : SplittingKernelQuotients.Rep Wl.ψ A B}
    (hN : ∀ p Φ, E (Wl.om A B χA χB p Φ) = N p (E Φ)) : HeisenbergWeilMatrices.IsWeil Wl.ψ (T.eChr χA) (T.eChr χB) N := by
  have hκ := isChange_kap hr.le
  refine ⟨fun p => ?_, fun p f => ?_, fun f w => ?_, fun g hg h hh f => ?_, fun v e he p hg hh => ?_⟩
  · exact (impl_iff hκ hE (hN p) p.1 p.2).1 (Wl.om_heis A B χA χB hr.ne hs.resA hs.resB p.1 p.2)
  · obtain ⟨Φ, rfl⟩ := E.surjective f
    rw [← hN]
    exact (unit_iff hκ hE Wl.ψ_std.1 hr.le _ _).1 fun μ 𝓕 hμ hF =>
      Wl.om_unit A B χA χB hr.ne hs.resA hs.resB μ 𝓕 hμ hF p Φ
  · obtain ⟨Φ, rfl⟩ := E.surjective f
    refine (Wl.om_cont A B χA χB hr.ne hs.resA hs.resB Φ (kap A B w)).congr fun p => ?_
    rw [← hN, ← hE]; rfl
  · obtain ⟨Φ, rfl⟩ := E.surjective f
    rw [← hN]
    exact (ev_zero hE _).symm.trans ((Wl.om_aut A B χA χB hr.ne hs.resA hs.resB g hg h hh Φ).trans (ev_zero hE _))
  · obtain ⟨g, h⟩ := p
    rw [scalar_eq hr.le]
    exact (actsBy_iff hκ hE (hN _) e _).1 (hm A B χA χB hr hs.resA hs.resB v e he g h ((suppAt_iff he A g).2 hg)
      ((suppAt_iff he B h).2 hh) _ _ ((isDetAt_iff he.idem A g _).2 rfl) ((isDetAt_iff he.idem B h _).2 rfl))

theorem exists_core_with (Wl : WeilTied D X T) (hm : ExactModulus Wl) (hc : Converges Wl)
    {P : ∀ A B : HSp D, (X.Sch A B → WA A B → ℂ) → Prop} (he : EqualRankWith T Wl.ψ P) :
    ∃ C : SplittingKernelQuotients.Core T, Match Wl C ∧
      ∀ (A B : HSp D) (hr : A.rank = B.rank), P A B fun Φ => (C.eUp A B hr.le Φ : WA A B → ℂ) := by
  have h1 : ∀ A B : HSp D, A.rank ≤ B.rank → ∃ E : X.Sch A B ≃ₗ[ℂ] HeisenbergWeilMatrices.Theta Wl.ψ A B,
      (A.rank = B.rank → P A B fun Φ => (E Φ : WA A B → ℂ)) ∧
      (A.rank < B.rank → ∀ Φ, Wl.evS A B Φ ∘ kap A B = E Φ) ∧
      ∀ χA χB, SplittingKernelQuotients.IsSplitting A B (T.eChr χA) (T.eChr χB) → ∃ om : SplittingKernelQuotients.Rep Wl.ψ A B,
        (A.rank < B.rank → ∀ p Φ, E (Wl.om A B χA χB p Φ) = om p (E Φ)) ∧
        HeisenbergWeilMatrices.IsWeil Wl.ψ (T.eChr χA) (T.eChr χB) om ∧ (A.SigOK → ∀ (Φ : X.Sch A B) (φ : X.cusp A) (h : GA D B),
          SplittingKernelQuotients.IsQuotInt A (T.petC A) (fun g => SplittingKernelQuotients.kern om (E Φ) g h * T.ev A (φ : X.AF A) g)
            (T.ev B (X.th A B χA χB Φ φ) h)) := by
    intro A B hle
    rcases hle.eq_or_lt with hr | hr
    · obtain ⟨E, hP, hE⟩ := he A B hr
      refine ⟨E, fun _ => hP, fun h => absurd hr h.ne, fun χA χB hs => ?_⟩
      obtain ⟨om, ho⟩ := hE χA χB hs
      exact ⟨om, fun h => absurd hr h.ne, ho⟩
    · obtain ⟨E, hE⟩ := exists_equiv (isChange_kap hle) Wl.ψ_std.1.1 _ (Wl.evS_inj A B) (Wl.evS_range A B hr.ne)
      refine ⟨E, fun h => absurd h hr.ne, fun _ => hE, fun χA χB hs => ?_⟩
      obtain ⟨N, hN⟩ : ∃ N : SplittingKernelQuotients.Rep Wl.ψ A B, ∀ p Φ, E (Wl.om A B χA χB p Φ) = N p (E Φ) :=
        ⟨E.conjRingEquiv.toMonoidHom.comp (Wl.om A B χA χB), fun p Φ =>
          congrArg (fun y => E (Wl.om A B χA χB p y)) (E.symm_apply_apply Φ).symm⟩
      refine ⟨N, fun _ => hN, isWeil_of_tied Wl hm hr hs hE hN, fun hsig Φ φ h => ?_⟩
      have k : ∀ g, SplittingKernelQuotients.kern N (E Φ) g h = Wl.evS A B (Wl.om A B χA χB (g, h) Φ) 0 := fun g => by
        rw [ev_zero hE, hN]; rfl
      have c := hc A B χA χB hr.ne hs.resA hs.resB hsig
      simp only [k]
      exact ⟨c.1, fun m hv => ⟨c.2 m hv Φ φ h, Wl.th A B χA χB hr.ne hs.resA hs.resB hsig m.1 m.2 hv Φ φ h⟩⟩
  choose eUp h10 h11 om h12 h13 h14 using h1
  choose eDn h2 using fun (A B : HSp D) (hr : A.rank < B.rank) =>
    exists_equiv (isChange_kapT hr) Wl.ψ_std.1.1 _ (Wl.evS_inj B A) (Wl.evS_range B A hr.ne')
  have dn : ∀ (A B : HSp D) (hr : A.rank < B.rank) χA χB hs g h Φ,
      eDn A B hr (Wl.om B A χB χA (h, g) Φ) = om A B hr.le χA χB hs (g, h) (eDn A B hr Φ) := by
    intro A B hr χA χB hs g h Φ
    have t : ∀ Φ Φ', (∀ x : WA A B, Wl.evS B A Φ' xᵀ = Wl.evS A B Φ x) ↔ eDn A B hr Φ' = eUp A B hr.le Φ := by
      intro Φ Φ'
      rw [(kap A B).surjective.forall, Subtype.ext_iff, ← h11 A B hr.le hr, ← h2, funext_iff]
      rfl
    obtain ⟨Φ₀, h0⟩ := (eUp A B hr.le).surjective (eDn A B hr Φ)
    rw [← h0, ← h12 A B hr.le χA χB hs hr, ← t]
    exact Wl.om_swap A B χA χB hr.ne hs.resA hs.resB g h Φ₀ Φ ((t _ _).2 h0.symm)
  refine ⟨⟨Wl.ψ, (stdChar_iff _).1 Wl.ψ_std, eUp, eDn, om, h13, h14, fun A B hr χA χB hs hsig Φ G g => ?_⟩, ⟨rfl,
    fun A B hr => ⟨h11 A B hr.le hr, h2 A B hr, fun χA χB hs g h => ⟨?_, ?_⟩⟩⟩, fun A B hr => h10 A B hr.le hr⟩
  · have k : ∀ h, SplittingKernelQuotients.kern (om A B hr.le χA χB hs) (eDn A B hr Φ) g h = Wl.evS B A (Wl.om B A χB χA (h, g) Φ) 0 :=
      fun h => by rw [ev_zero (h2 A B hr), dn A B hr χA χB hs]; rfl
    have c := hc B A χB χA hr.ne' hs.resB hs.resA hsig
    simp only [k]
    exact ⟨c.1, fun m hv => ⟨c.2 m hv Φ G g, Wl.th B A χB χA hr.ne' hs.resB hs.resA hsig m.1 m.2 hv Φ G g⟩⟩
  · exact LinearMap.ext fun Φ => (LinearEquiv.eq_symm_apply _).2 (h12 A B hr.le χA χB hs hr _ Φ)
  · exact LinearMap.ext fun Φ => (LinearEquiv.eq_symm_apply _).2 (dn A B hr χA χB hs g h Φ)

theorem exists_core (Wl : WeilTied D X T) (hm : ExactModulus Wl) (hc : Converges Wl) (he : EqualRank T Wl.ψ) :
    ∃ C : SplittingKernelQuotients.Core T, Match Wl C :=
  (exists_core_with Wl hm hc (P := fun _ _ _ => True) fun A B hr => (he A B hr).imp fun _ h => ⟨trivial, h⟩).imp
    fun _ h => h.1

open Classical in

def junkSig (X : ThetaX D) (J : ∀ V W, X.Sch V W →ₗ[ℂ] X.cusp V →ₗ[ℂ] X.AF W) : ThetaX D :=
  { X with th := fun V W χ χ' => if V.SigOK then X.th V W χ χ' else J V W }

structure Beyond (Wl : WeilTied D X T) : Prop where
  modulus : ExactModulus Wl
  converges : Converges Wl
  equalRank : EqualRankPure T Wl.ψ
  fact : FactPure Wl
  offChars : SplittingKernelQuotients.OffChars T
  offSig : SplittingKernelQuotients.OffSig X

end GlobalTheory.WeilTieCompare

end
