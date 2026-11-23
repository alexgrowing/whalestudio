import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.InfinitesimalCharacterLimits.LimitPairSpaces.MultTendsto
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CommuteRtOfMemZalg
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.InfinitesimalCharacterLimits.TensorOperatorTrees.TrStable
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.InfinitesimalCharacterLimits.TensorOperatorTrees.TwShift

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Formalism.L2.Host Filter Topology
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DiscSpec GlobalTheory.CompanionTheory.CTFin PositivityTheory.Rg.Rs

namespace PositivityTheory.Rg.BcB.SpectralAccumulation.LV

open PositivityTheory.Rg.BcB.SpectralAccumulation PositivityTheory.Rg.BcB.E

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem allLeaves_stable_of_disc {N : ℕ} (t : Tr E N) (h : t.Disc) : t.AllLeaves fun _ V => IsStable V := by
  induction t with
  | leaf V z =>
    rcases h with ⟨_, rfl, _⟩ | ⟨_, hV⟩
    · exact fun _ _ _ => Submodule.mem_top
    · exact hV.stable
  | node t₁ t₂ ih₁ ih₂ => exact ⟨ih₁ h.1, ih₂ h.2⟩

theorem disc_of_good {N : ℕ} (t : Tr E N) (h : t.Good) : t.Disc := by
  induction t with
  | leaf V z =>
    rcases h with h | ⟨h1, h2, _⟩
    · exact Or.inl h
    · exact Or.inr ⟨h1, h2⟩
  | node t₁ t₂ ih₁ ih₂ => exact ⟨ih₁ h.1, ih₂ h.2⟩

theorem allLeaves_strip {N : ℕ} (t : Tr E N) (P : ∀ M : ℕ, Submodule ℂ (Sm E M) → Prop) :
    t.strip.AllLeaves P ↔ t.AllLeaves P := by
  induction t with
  | leaf V z => exact Iff.rfl
  | node t₁ t₂ ih₁ ih₂ => exact and_congr ih₁ ih₂

theorem allLeaves_addTw {N : ℕ} (t : Tr E N) (α : ℕ → ℂ) (P : ∀ M : ℕ, Submodule ℂ (Sm E M) → Prop) :
    (t.addTw α).AllLeaves P ↔ t.AllLeaves P := by
  induction t generalizing α with
  | leaf V z => exact Iff.rfl
  | node t₁ t₂ ih₁ ih₂ => exact and_congr (ih₁ _) (ih₂ _)

theorem strip_twists_length {N : ℕ} (t : Tr E N) : t.strip.twists.length = t.twists.length := by
  induction t with
  | leaf V z => rfl
  | node t₁ t₂ ih₁ ih₂ =>
    change (t₁.strip.twists ++ t₂.strip.twists).length = (t₁.twists ++ t₂.twists).length
    rw [List.length_append, List.length_append, ih₁, ih₂]

theorem addTw_congr {N : ℕ} (t : Tr E N) {α α' : ℕ → ℂ} (h : ∀ i < t.twists.length, α i = α' i) :
    t.addTw α = t.addTw α' := by
  induction t generalizing α α' with
  | leaf V z =>
    change Tr.leaf V (z + α 0) = Tr.leaf V (z + α' 0)
    rw [h 0 (by simp [Tr.twists])]
  | node t₁ t₂ ih₁ ih₂ =>
    have hl : (Tr.node t₁ t₂).twists.length = t₁.twists.length + t₂.twists.length := by
      change (t₁.twists ++ t₂.twists).length = _
      rw [List.length_append]
    change Tr.node (t₁.addTw α) (t₂.addTw fun i => α (i + t₁.twists.length)) =
      Tr.node (t₁.addTw α') (t₂.addTw fun i => α' (i + t₁.twists.length))
    rw [ih₁ (fun i hi => h i (by omega)), ih₂ (fun i hi => h (i + t₁.twists.length) (by omega))]

theorem eq_addTw {N : ℕ} (t : Tr E N) : t = t.strip.addTw fun i => t.twists.getD i 0 := by
  induction t with
  | leaf V z =>
    change Tr.leaf V z = Tr.leaf V (0 + z)
    rw [zero_add]
  | node t₁ t₂ ih₁ ih₂ =>
    change Tr.node t₁ t₂ = Tr.node (t₁.strip.addTw fun i => (t₁.twists ++ t₂.twists).getD i 0)
      (t₂.strip.addTw fun i => (t₁.twists ++ t₂.twists).getD (i + t₁.strip.twists.length) 0)
    have e₁ : t₁.strip.addTw (fun i => (t₁.twists ++ t₂.twists).getD i 0) =
        t₁.strip.addTw fun i => t₁.twists.getD i 0 := by
      refine addTw_congr _ fun i hi => ?_
      rw [strip_twists_length] at hi
      exact List.getD_append _ _ _ _ hi
    have e₂ : t₂.strip.addTw (fun i => (t₁.twists ++ t₂.twists).getD (i + t₁.strip.twists.length) 0) =
        t₂.strip.addTw fun i => t₂.twists.getD i 0 := by
      refine addTw_congr _ fun i _ => ?_
      rw [strip_twists_length, List.getD_append_right _ _ _ _ (by omega), Nat.add_sub_cancel]
    rw [e₁, e₂, ← ih₁, ← ih₂]

def mulOp {N : ℕ} (f : GA E N → ℂ) (hf : f ∈ Sm E N) : Sm E N →ₗ[ℂ] Sm E N where
  toFun φ := ⟨fun x => f x * φ.1 x, mul_mem_Sm' hf φ.2⟩
  map_add' φ ψ := Subtype.ext (funext fun x => by
    show f x * (φ.1 x + ψ.1 x) = f x * φ.1 x + f x * ψ.1 x
    ring)
  map_smul' c φ := Subtype.ext (funext fun x => by
    show f x * (c * φ.1 x) = c * (f x * φ.1 x)
    ring)

theorem mulOp_val {N : ℕ} (f : GA E N → ℂ) (hf : f ∈ Sm E N) (φ : Sm E N) :
    (mulOp f hf φ).1 = fun x => f x * φ.1 x := rfl

theorem mulOp_mulChi {N : ℕ} (f : GA E N → ℂ) (hf : f ∈ Sm E N) (χ : HChar E) (ψ : Sm E N) :
    mulOp f hf (mulChi N χ ψ) = mulChi N χ (mulOp f hf ψ) := Subtype.ext (funext fun x => by
  show f x * (mulChi N χ ψ).1 x = (mulChi N χ (mulOp f hf ψ)).1 x
  rw [mulChi_apply, mulChi_apply]
  show f x * (ψ.1 x * _) = (f x * ψ.1 x) * _
  ring)

theorem mult_node_unip {r s : ℕ} (t₁ : Tr E r) (t₂ : Tr E s) (γ : ℕ → ℂ) (u : BlockIx (r + s) r → Ad E)
    (x : GA E (r + s)) : mult (Tr.node t₁ t₂) γ (unip u * x) = mult (Tr.node t₁ t₂) γ x := by
  obtain ⟨q, hc, hx⟩ := exists_decI (r := r) (s := s) x
  rw [hx, ← mul_assoc, ← mul_assoc, ← InducedTensorMap.D.unip_add', mult_node _ _ _ _ _ _ hc, mult_node _ _ _ _ _ _ hc]

theorem finGL_unip' {r s : ℕ} (x : BlockIx (r + s) r → Af E) :
    finGL E (r + s) (unip x) = unip fun p => sFin E (x p) := by
  refine ga_ext ?_ ?_
  · rw [pInf_finGL, IwaAd.map_unip]
    have h0 : (fun p => pInf E (sFin E (x p))) = 0 := funext fun p => map_zero (infEq E).symm
    rw [h0, InducedTensorMap.unip_zero]
  · rw [pFin_finGL, IwaAd.map_unip]
    rfl

theorem lev_mul_cf_int {r s : ℕ} (k : Kinf E (r + s)) (g : GL (Fin (r + s)) (Af E)) :
    ∃ (mf : GL (Fin r) (Af E) × GL (Fin s) (Af E)) (c : GL (Fin (r + s)) (Af E)), c ∈ Cint E (r + s) ∧
      ∀ m : GA E r × GA E s, ∃ v : BlockIx (r + s) r → Ad E,
        lev (Ad E) r s m * (infGL E (r + s) (Unitary.toUnits k) * finGL E (r + s) g) =
          unip v * lev (Ad E) r s (m.1 * finGL E r mf.1, m.2 * finGL E s mf.2) * InducedTensorMap.cf (r + s) k c := by
  obtain ⟨xf, mf, c, hc, hg⟩ := IwaFin.exists_unip_lev_integral E r s g
  refine ⟨mf, c, hc, fun m => ?_⟩
  obtain ⟨v, hv⟩ := InducedTensorMap.lev_mul_unip m fun p => sFin E (xf p)
  refine ⟨v, ?_⟩
  have h1 : infGL E (r + s) (Unitary.toUnits k) * finGL E (r + s) g =
      (unip fun p => sFin E (xf p)) * lev (Ad E) r s (finGL E r mf.1, finGL E s mf.2) *
        InducedTensorMap.cf (r + s) k c := by
    calc infGL E (r + s) (Unitary.toUnits k) * finGL E (r + s) g
        = infGL E (r + s) (Unitary.toUnits k) * (finGL E (r + s) (unip xf * lev (Af E) r s mf) *
            finGL E (r + s) c) := by rw [hg, map_mul]
      _ = finGL E (r + s) (unip xf * lev (Af E) r s mf) *
            (infGL E (r + s) (Unitary.toUnits k) * finGL E (r + s) c) := by
          rw [← mul_assoc, infGL_comm, mul_assoc]
      _ = _ := by
          rw [map_mul, finGL_unip', Slice1.lev_finGL]
          rfl
  rw [h1, ← mul_assoc, ← mul_assoc, hv, mul_assoc (unip v), ← map_mul]
  rfl

theorem act_fin_apply' {N : ℕ} (g : GL (Fin N) (Af E)) (φ : Sm E N) (x : GA E N) :
    (act (.fin g) φ).1 x = φ.1 (x * finGL E N g) := rfl

theorem mult_operator_shifts_twist {N : ℕ} (b : Tr E N) : ∀ (α β : ℕ → ℂ), (b.AllLeaves fun _ V => IsStable V) →
    ∀ φ ∈ (b.addTw α).space, mulOp (mult b fun i => β i - α i) (mult_mem_Sm b _) φ ∈ (b.addTw β).space := by
  induction b with
  | leaf V z =>
    intro α β _
    rintro _ ⟨ψ, hψ, rfl⟩
    refine ⟨ψ, hψ, Subtype.ext (funext fun x => ?_)⟩
    change ((mulChi _ (Model.absC E (z + β 0))) ψ).1 x =
      mult (Tr.leaf V z) (fun i => β i - α i) x * ((mulChi _ (Model.absC E (z + α 0))) ψ).1 x
    rw [mult_leaf, mulChi_apply, mulChi_apply, ExponentTwist.chiDet_absC_val, ExponentTwist.chiDet_absC_val,
      ExponentTwist.chiDet_absC_val]
    have e : ∀ L : ℂ, Complex.exp ((z + β 0) * L) =
        Complex.exp ((β 0 - α 0) * L) * Complex.exp ((z + α 0) * L) := fun L => by
      rw [← Complex.exp_add]
      ring_nf
    rw [e]
    ring
  | @node r s t₁ t₂ ih₁ ih₂ =>
    intro α β hb φ hφ
    obtain ⟨hb₁, hb₂⟩ := hb
    set L := t₁.twists.length with hL
    set α' : ℕ → ℂ := fun i => α (i + L) with hα'
    set β' : ℕ → ℂ := fun i => β (i + L) with hβ'
    have hU₁ : IsStable (t₁.addTw α).space := Trees.isStable_space _ ((allLeaves_addTw _ _ _).2 hb₁)
    have hU₁' : IsStable (t₁.addTw β).space := Trees.isStable_space _ ((allLeaves_addTw _ _ _).2 hb₁)
    have hU₂ : IsStable (t₂.addTw α').space := Trees.isStable_space _ ((allLeaves_addTw _ _ _).2 hb₂)
    have hU₂' : IsStable (t₂.addTw β').space := Trees.isStable_space _ ((allLeaves_addTw _ _ _).2 hb₂)

    have hA : ∀ (z : ℂ) (h : GL (Fin r) (Af E)), ∀ ψ ∈ tw (t₁.addTw α).space z, ∃ χ ∈ tw (t₁.addTw β).space z,
        χ.1 = fun m => mult t₁ (fun i => β i - α i) (m * finGL E r h) * ψ.1 m := by
      intro z h ψ hψ
      have h1 : act (.fin h⁻¹) ψ ∈ tw (t₁.addTw α).space z := ParabolicProjection.isStable_tw hU₁ z _ _ hψ
      obtain ⟨ρ, hρ, hρe⟩ := h1
      have h2 : mulOp (mult t₁ fun i => β i - α i) (mult_mem_Sm t₁ _) (act (.fin h⁻¹) ψ) ∈
          tw (t₁.addTw β).space z := by
        rw [← hρe]
        show mulOp _ _ ((mulChi r (Model.absC E z)) ρ) ∈ _
        rw [mulOp_mulChi]
        exact ⟨_, ih₁ α β hb₁ ρ hρ, rfl⟩
      refine ⟨act (.fin h) (mulOp (mult t₁ fun i => β i - α i) (mult_mem_Sm t₁ _) (act (.fin h⁻¹) ψ)),
        ParabolicProjection.isStable_tw hU₁' z _ _ h2, funext fun m => ?_⟩
      simp only [act_fin_apply', mulOp_val]
      rw [mul_assoc m, ← map_mul, mul_inv_cancel, map_one, mul_one]
    have hB : ∀ (z : ℂ) (h : GL (Fin s) (Af E)), ∀ ψ ∈ tw (t₂.addTw α').space z, ∃ χ ∈ tw (t₂.addTw β').space z,
        χ.1 = fun m => mult t₂ (fun i => β' i - α' i) (m * finGL E s h) * ψ.1 m := by
      intro z h ψ hψ
      have h1 : act (.fin h⁻¹) ψ ∈ tw (t₂.addTw α').space z := ParabolicProjection.isStable_tw hU₂ z _ _ hψ
      obtain ⟨ρ, hρ, hρe⟩ := h1
      have h2 : mulOp (mult t₂ fun i => β' i - α' i) (mult_mem_Sm t₂ _) (act (.fin h⁻¹) ψ) ∈
          tw (t₂.addTw β').space z := by
        rw [← hρe]
        show mulOp _ _ ((mulChi s (Model.absC E z)) ρ) ∈ _
        rw [mulOp_mulChi]
        exact ⟨_, ih₂ α' β' hb₂ ρ hρ, rfl⟩
      refine ⟨act (.fin h) (mulOp (mult t₂ fun i => β' i - α' i) (mult_mem_Sm t₂ _) (act (.fin h⁻¹) ψ)),
        ParabolicProjection.isStable_tw hU₂' z _ _ h2, funext fun m => ?_⟩
      simp only [act_fin_apply', mulOp_val]
      rw [mul_assoc m, ← map_mul, mul_inv_cancel, map_one, mul_one]
    set Φ := mult (Tr.node t₁ t₂) fun i => β i - α i with hΦ
    have hΦS : Φ ∈ Sm E (r + s) := mult_mem_Sm _ _
    change φ ∈ Submodule.span ℂ _ at hφ
    change _ ∈ Submodule.span ℂ _
    induction hφ using Submodule.span_induction with
    | mem φ h =>
      obtain ⟨⟨hu, hsl⟩, hK⟩ := h
      refine Submodule.subset_span ⟨⟨fun x g => ?_, fun k g => ?_⟩, ?_⟩
      · change Φ (unip x * g) * φ.1 (unip x * g) = Φ g * φ.1 g
        rw [hΦ, mult_node_unip, hu x g]
      · obtain ⟨mf, c, hc, hdec⟩ := lev_mul_cf_int (r := r) (s := s) k g
        obtain ⟨n, ψ₁, ψ₂, h₁, h₂, e⟩ := InducedTensorMap.tensor_pair_finite_sum (hsl k g)
        choose χ₁ hχ₁ eχ₁ using fun i => hA _ mf.1 (ψ₁ i) (h₁ i)
        choose χ₂ hχ₂ eχ₂ using fun i => hB _ mf.2 (ψ₂ i) (h₂ i)
        have key := ParabolicProjection.sum_mem_tens2 (V₁ := tw (t₁.addTw β).space ((s : ℂ) / 2))
          (V₂ := tw (t₂.addTw β').space (-(r : ℂ) / 2)) hχ₁ hχ₂
        convert key using 1
        funext m
        obtain ⟨v, hv⟩ := hdec m
        have e2 := congrFun e m
        try simp only at e2
        change Φ (lev (Ad E) r s m * (infGL E (r + s) (Unitary.toUnits k) * finGL E (r + s) g)) *
          φ.1 (lev (Ad E) r s m * (infGL E (r + s) (Unitary.toUnits k) * finGL E (r + s) g)) = _
        rw [e2, hv, hΦ, mult_node _ _ _ _ _ _ hc, Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [eχ₁ i, eχ₂ i]
        ring
      · have hK' : FiniteDimensional ℂ (Submodule.span ℂ (Set.range fun k => cptRep E (r + s) k φ)) := hK
        change FiniteDimensional ℂ (Submodule.span ℂ (Set.range fun k => cptRep E (r + s) k (mulOp Φ hΦS φ)))
        have e : (Set.range fun k => cptRep E (r + s) k (mulOp Φ hΦS φ)) =
            (mulOp Φ hΦS) '' Set.range fun k => cptRep E (r + s) k φ := by
          rw [← Set.range_comp]
          congr 1
          funext k
          refine Subtype.ext (funext fun x => ?_)
          change Φ (x * infGL E (r + s) (Unitary.toUnits k)) * φ.1 (x * infGL E (r + s) (Unitary.toUnits k)) =
            Φ x * φ.1 (x * infGL E (r + s) (Unitary.toUnits k))
          have e1 : x * infGL E (r + s) (Unitary.toUnits k) = x * InducedTensorMap.cf (r + s) k 1 := by
            simp [InducedTensorMap.cf]
          rw [e1, hΦ, mult_rinv _ _ _ _ (one_mem _)]
        rw [e, Submodule.span_image]
        infer_instance
    | zero => rw [map_zero]; exact Submodule.zero_mem _
    | add a b _ _ ha hb => rw [map_add]; exact Submodule.add_mem _ ha hb
    | smul c a _ ha => rw [map_smul]; exact Submodule.smul_mem _ c ha

theorem flat {N : ℕ} (b : Tr E N) (hb : b.AllLeaves fun _ V => IsStable V) (α β : ℕ → ℂ) (φ : Sm E N)
    (hφ : φ ∈ (b.addTw α).space) :
    ∃ ψ ∈ (b.addTw β).space, ψ.1 = fun x => mult b (fun i => β i - α i) x * φ.1 x :=
  ⟨_, mult_operator_shifts_twist b α β hb φ hφ, rfl⟩

end PositivityTheory.Rg.BcB.SpectralAccumulation.LV

end
