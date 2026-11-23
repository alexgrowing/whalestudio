import Development.WeilBound.CoreStatements.VolumeEquality.DegPushMuLinkA
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.DetLatticeFlagTensorStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IntersectionDatumDegreeSumStatement

noncomputable section

namespace SheetDecomposition

open AlgebraicGeometry CategoryTheory NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp

def muRev (p q : ℕ) (m : Fin q) : Fin (p + q) := ⟨p + q - 1 - m, by have := m.2; omega⟩

theorem muDeg_eq {Ψ K : Type} [Fintype Ψ] {p q : ℕ} (x : Ψ × Fin (p + q) → K → ℤ) :
    muDeg x = ∑ τ, ∑ m : Fin q, x (τ, muRev p q m) := by
  refine Finset.sum_congr rfl fun τ _ => (Finset.sum_bij (fun m _ => muRev p q m) ?_ ?_ ?_ fun _ _ => rfl).symm
  · intro m _
    have := m.2
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, muRev]
    omega
  · intro a _ b _ h
    have h := congrArg Fin.val h
    have := a.2
    have := b.2
    simp only [muRev] at h
    exact Fin.ext (by omega)
  · intro i hi
    have h1 := (Finset.mem_filter.1 hi).2
    have h2 := i.2
    exact ⟨⟨p + q - 1 - i, by omega⟩, Finset.mem_univ _, Fin.ext (by simp only [muRev]; omega)⟩

theorem mu_mono_sum {Ω K I : Type} [Field Ω] [Fintype K] (z : K → Ω) (hz : ∀ k, z k ≠ 0) (s : Finset I) (a : I → K → ℤ) :
    ∏ k, z k ^ (∑ j ∈ s, a j) k = ∏ j ∈ s, ∏ k, z k ^ a j k := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert j s hj ih =>
    rw [Finset.sum_insert hj, Finset.prod_insert hj, ← ih, ← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun k _ => zpow_add₀ (hz k) _ _

section

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Tor.Level H} {Xo : Moduli D l}
  {c : Coeff l} {Y : Model Xo c (algebraMap (𝓞 c.F) c.F)} {S' : Finset ℕ} {Ω' : Type} [Field Ω'] {K' : Type} [Fintype K']
  {J' : K' → Type} [∀ k, Fintype (J' k)] {y' : (Σ k, J' k) → Ω'} {𝔐' : HodgeCpt Y S' y'} (Fl : 𝔐'.Flag)

omit [∀ k, Fintype (J' k)] in
theorem mu_rootLat (τ : CMType H) (m : Fin D.q) : Fl.rootLat (τ, muRev D.p D.q m) =
    Lat.tens (fun _ : Unit => (𝔐'.V (.inr τ)).gr (Fl.b (.inr τ)) m) fun _ => -1 := by
  have hm := m.2
  have h0 : ¬ ((muRev D.p D.q m : ℕ) < D.p) := by simp only [muRev]; omega
  have h1 : HodgeCpt.rootIdx D (τ, muRev D.p D.q m) = ⟨.inr τ, m⟩ := by
    unfold HodgeCpt.rootIdx
    rw [dif_neg h0]
    congr 1
    exact Fin.ext (by simp only [muRev]; omega)
  have h2 : HodgeCpt.rootSgn D (τ, muRev D.p D.q m) = -1 := if_neg h0
  unfold HodgeCpt.Flag.rootLat
  rw [h1, h2]

theorem mu_flag_side (hC : ChartVal) {x : CMType H × Fin (D.p + D.q) → K' → ℤ} {e : CMType H × Fin (D.p + D.q) → Ω'}
    (hR : Fl.RootLines x e) (hb : ∀ s, LinearIndependent Ω' (Fl.b s)) {Ω₃ : Type} [Field Ω₃] {O : ValuationSubring Ω₃}
    {i : Ω' →+* Ω₃} {q : Cpt 𝔐'.ξ} (hD : Dom O i 𝔐'.ξ q) {t : CMType H → Ω'}
    (ht : ∀ τ, (detLat (𝔐'.V (.inr τ)) (Fl.b (.inr τ))).IsGenAt q (t τ)) :
    vdeg O (fun a => i (y' a)) (muDeg x) * O.valuation (i (∏ τ, ∏ m, e (τ, muRev D.p D.q m))) * O.valuation (i (∏ τ, t τ)) = 1 := by
  obtain ⟨ch, hch⟩ := 𝔐'.tie.cover q
  have hz : ∀ k, y' ⟨k, ch k⟩ ≠ 0 := fun k => Finset.prod_ne_zero_iff.1 hch.1 k (Finset.mem_univ _)
  have g1 := fun τ m => mu_deg_gen (hR (τ, muRev D.p D.q m)) hch
  simp only [mu_rootLat] at g1
  choose g hg using fun τ m => mu_tens_ex (g1 τ m)
  have v1 : ∀ τ m, O.valuation (i ((∏ k, y' ⟨k, ch k⟩ ^ x (τ, muRev D.p D.q m) k) * e (τ, muRev D.p D.q m))) *
      O.valuation (i (g τ m ())) = 1 := fun τ m => by
    rw [mu_gen_val hD (g1 τ m) (mu_tens_gen _ (hg τ m)), ← map_mul, ← map_mul]
    simp [(hg τ m ()).1]
  have v2 : ∀ τ, O.valuation (i (t τ)) = ∏ m, O.valuation (i (g τ m ())) := fun τ => by
    have h := ht τ
    rw [GlobalTheory.T.det_lattice_flag_tensor _ _ _ _ _ _ _ (hb _) (Fl.sub _)] at h
    rw [mu_gen_val hD h (mu_tens_gen _ fun m => hg τ m ())]
    simp only [zpow_one, map_prod]
    rfl
  rw [hC _ _ _ O i _ q _ _ y' ch _ hD hch, muDeg_eq, mu_mono_sum _ hz]
  simp only [mu_mono_sum _ hz, map_prod O.valuation, map_prod i (s := Finset.univ (α := CMType H)),
    map_prod i (s := Finset.univ (α := Fin D.q)), v2, ← Finset.prod_mul_distrib]
  refine Finset.prod_eq_one fun τ _ => Finset.prod_eq_one fun m _ => ?_
  rw [← v1 τ m, map_mul, map_mul]

end

theorem muLink : ChartVal → Centre → CoordLat → MuLink := by
  intro hC hZ hL E _ _ _ _ H D Xo l c Y S' Ω' _ K' _ J' _ y' 𝔐' Fl x e II K _ J _ Ω _ _ W _ _ Dc Hd S₀ Or ψ Ω₃ _ _ i₁ i₂ hR hbg hsm hS
    hψ hi
  classical
  obtain ⟨b, u, hb, -, -, hFl, -, -, hstep, -⟩ := Fl.generic
  obtain ⟨A, hA, hj, hoth⟩ := hL E H D l (Xo l) c Y S' Ω' K' J' y' 𝔐' Fl b hb
  obtain ⟨b₁, hb₁, hA₁⟩ := hoth S₀ Ω K J Dc.y Or.𝔐 ψ hψ
  have hmem : ∀ s m, Fl.b s m ∈ 𝔐'.Vgen s := fun s m => by
    have h1 : Fl.b s m ∈ flagStep Ω' (Fl.b s) (labelRk D s) := Submodule.subset_span ⟨m, m.2, rfl⟩
    rw [hstep] at h1
    refine (Submodule.span_le.2 ?_ : _ ≤ 𝔐'.Vgen s) h1
    rintro _ ⟨k, -, rfl⟩
    exact Submodule.sum_mem _ fun a _ => Submodule.smul_mem _ _ ((hj s).2 ▸ Submodule.subset_span ⟨a, rfl⟩)
  obtain ⟨ch₀, hch₀⟩ := Or.𝔐.tie.cover ⟨genPt Or.𝔐.ξ, specializes_rfl⟩
  obtain ⟨n, f, cc, -, -, hsum, hloc⟩ := Hd.locally ch₀ hch₀.1
  obtain ⟨l₀⟩ : Nonempty (Fin n) := by
    by_contra h
    have := not_nonempty_iff.1 h
    simp at hsum
  obtain ⟨bb, -, w, -, hΛ⟩ := hloc l₀
  have hs : ∀ τ k, ∃ z, z ∈ Or.𝔐.Vgen (Or.sm τ) ∧ Or.i τ (bb τ (tailIdx Dc.j_le_N k)) - z ∈ Or.𝔐.Vgen (Or.bg τ) := fun τ k => by
    obtain ⟨a, ha, z, hz, h⟩ := Submodule.mem_sup.1
      (Or.i_range τ ▸ LinearMap.mem_range_self (Or.i τ) (bb τ (tailIdx Dc.j_le_N k)))
    exact ⟨z, hz, by rw [← h, add_sub_cancel_right]; exact ha⟩
  choose s hs using hs
  obtain ⟨hsi, hdeg⟩ := GlobalTheory.T.intersection_datum_degree_sum E H D Xo l c Y II K J Ω W Dc Hd S₀ Or 0 bb s _ hs hΛ
  have hSB : Dc.SB 0 = ∅ := by simp [ComponentData.SB, hS]
  have hmu : muTwDeg Hd 0 = Hd.aMu := by simp [muTwDeg, hSB]
  rw [hmu, hSB, Finset.union_empty, hsm] at hdeg
  obtain ⟨e₁, hdeg⟩ : ∃ e₁, (Lat.tens (fun τ => detLat (Or.𝔐.V (.inr τ)) (s τ)) fun _ => -1).IsDegOn Set.univ Dc.y Hd.aMu e₁ :=
    ⟨_, hdeg⟩
  have hrk : ∀ τ : CMType H, labelRk D (.inr τ) = Dc.N - Dc.j := fun τ => by
    have := Or.rk_sm τ
    rwa [hsm] at this
  choose ρ₁ hρ₁ h₁ using fun τ => mu_side (Ω₃ := Ω₃) (Or.𝔐.V (.inr τ)) (hrk τ) _ (Or.𝔐.vb _) _ (hb₁ _).1 (hb₁ _).2 (s τ) (hsi τ)
    fun k => by
      have := (hs τ k).1
      rwa [hsm] at this
  choose ρ₂ hρ₂ h₂ using fun τ => mu_side (Ω₃ := Ω₃) (𝔐'.V (.inr τ)) rfl _ (𝔐'.vb _) _ (hj _).1 (hj _).2 (Fl.b (.inr τ)) (hFl _)
    (hmem _)
  have n1 : i₁ (∏ τ, ρ₁ τ) ≠ 0 := (map_ne_zero _).2 (Finset.prod_ne_zero_iff.2 fun τ _ => hρ₁ τ)
  have n2 : i₂ (∏ τ, ρ₂ τ) ≠ 0 := (map_ne_zero _).2 (Finset.prod_ne_zero_iff.2 fun τ _ => hρ₂ τ)
  have n3 : i₂ (∏ τ, ∏ m, e (τ, muRev D.p D.q m)) ≠ 0 :=
    (map_ne_zero _).2 (Finset.prod_ne_zero_iff.2 fun τ _ => Finset.prod_ne_zero_iff.2 fun m _ => (hR _).1)
  refine ⟨i₁ e₁ * i₂ (∏ τ, ρ₂ τ) / (i₁ (∏ τ, ρ₁ τ) * i₂ (∏ τ, ∏ m, e (τ, muRev D.p D.q m))),
    div_ne_zero (mul_ne_zero ((map_ne_zero _).2 hdeg.1) n2) (mul_ne_zero n1 n3), fun O hO => ?_⟩
  obtain ⟨q, q', hD, hD', hq⟩ := hZ E H D l (Xo l) c Y S₀ S' Ω Ω' Ω₃ K K' J J' Dc.y y' Or.𝔐 𝔐' i₁ i₂ O (by
    have e1 : Or.𝔐.ξ ≫ Or.𝔐.f = spMap ψ ≫ 𝔐'.ξ₀ := hψ
    have e2 : 𝔐'.ξ ≫ 𝔐'.f = spMap 𝔐'.fn ≫ 𝔐'.ξ₀ := 𝔐'.fn_over
    rw [e1, e2, ← Category.assoc, ← Category.assoc, ← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
      ← CommRingCat.ofHom_comp, hi])
  choose t₁ T₁ g₁ d₁ sp₁ using fun τ => h₁ τ q O i₁ _ ψ _ hD (hA₁ q (mu_char0 hD hO) (.inr τ))
  choose t₂ T₂ g₂ d₂ sp₂ using fun τ => h₂ τ q' O i₂ _ 𝔐'.fn _ hD' (hA q' (mu_char0 hD' hO) (.inr τ))
  have hi' : ∀ a, i₁ (ψ a) = i₂ (𝔐'.fn a) := fun a => DFunLike.congr_fun hi a
  have k3 : O.valuation (i₁ (∏ τ, ρ₁ τ)) * O.valuation (i₁ (∏ τ, t₁ τ)) =
      O.valuation (i₂ (∏ τ, ρ₂ τ)) * O.valuation (i₂ (∏ τ, t₂ τ)) := by
    simp only [map_prod, ← Finset.prod_mul_distrib, ← map_mul, ← d₁, ← d₂]
    refine Finset.prod_congr rfl fun τ _ => mu_det_eq O _ _ ?_
    rw [sp₁, sp₂, hq]
    simp only [hi']
  have k2 := mu_flag_side Fl hC hR hFl hD' g₂
  obtain ⟨ch, hch⟩ := Or.𝔐.tie.cover q
  have k1 : vdeg O (fun a => i₁ (Dc.y a)) Hd.aMu * O.valuation (i₁ e₁) * O.valuation (i₁ (∏ τ, t₁ τ)) = 1 := by
    rw [hC _ _ _ O i₁ _ q _ _ Dc.y ch _ hD hch, ← map_mul O.valuation (i₁ _) (i₁ e₁), ← map_mul i₁, mu_gen_val hD (mu_deg_gen hdeg hch) (mu_tens_gen _ g₁),
      ← map_mul, ← map_mul, ← Finset.prod_mul_distrib, Finset.prod_eq_one fun τ _ => by simp [(g₁ τ).1]]
    simp
  rw [map_div₀, map_mul, map_mul]
  exact mu_alg k1 k2 k3 ((map_ne_zero _).2 n1)

end SheetDecomposition
