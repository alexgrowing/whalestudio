import Formalism.LocalRingCardinality.SpanPowerMembership.NZRowF

noncomputable section

namespace Formalism.BasicNotions.Examples₂.NZ

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.Examples₂

section Gen

variable {D : D7} {EE : Type} [NormedAddCommGroup EE] [InnerProductSpace ℂ EE] [FiniteDimensional ℂ EE]
  (S : RowSide D EE)

theorem inj_of_iso {μ} (hiso : ∀ x y, inner ℂ (S.iota μ x) (S.iota μ y) = inner ℂ x y) :
    Function.Injective (S.iota μ) := by
  rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
  intro x hx
  have := hiso x x
  rw [LinearMap.mem_ker.mp hx, inner_zero_left] at this
  exact inner_self_eq_zero.mp this.symm

theorem iotaQ_bij {μ} (he : S.eOp μ = LinearMap.id)
    (hiso : ∀ x y, inner ℂ (S.iota μ x) (S.iota μ y) = inner ℂ x y)
    (hs : Function.Surjective (S.iota μ)) : Function.Bijective (S.iotaQ μ) := by
  have hi := inj_of_iso S hiso
  refine ⟨fun a b h => Subtype.ext (hi h), fun y => ?_⟩
  obtain ⟨z, rfl⟩ := hs y
  exact ⟨⟨z, by rw [Qsp_top S he hi]; trivial⟩, rfl⟩

theorem iotaQ_adj {μ} (he : S.eOp μ = LinearMap.id)
    (hiso : ∀ x y, inner ℂ (S.iota μ x) (S.iota μ y) = inner ℂ x y)
    (hs : Function.Surjective (S.iota μ)) : S.iotaQ μ ∘ₗ LinearMap.adjoint (S.iotaQ μ) = LinearMap.id := by
  have hi := inj_of_iso S hiso
  ext x
  refine ext_inner_right ℂ fun y => ?_
  obtain ⟨z, rfl⟩ := hs y
  have hz : z ∈ S.Qsp μ := by rw [Qsp_top S he hi]; trivial
  show inner ℂ (S.iota μ (LinearMap.adjoint (S.iotaQ μ) x : S.Amb μ)) (S.iota μ z) = inner ℂ x (S.iota μ z)
  rw [hiso]
  have h1 : inner ℂ (LinearMap.adjoint (S.iotaQ μ) x) (⟨z, hz⟩ : S.Qsp μ) =
      inner ℂ x (S.iotaQ μ ⟨z, hz⟩) := LinearMap.adjoint_inner_left _ _ _
  exact h1

theorem latticeBound_one {n : ℕ} (b : OrthonormalBasis (Fin n) ℂ EE) (ty : Fin n → D.what₂.FT)
    (he : ∀ μ, S.eOp μ = LinearMap.id)
    (hiso : ∀ μ x y, inner ℂ (S.iota μ x) (S.iota μ y) = inner ℂ x y)
    (hs : ∀ μ, Function.Surjective (S.iota μ)) (hl : ∀ μ j π, D.what₂.lamP μ j π = 1) : S.RowLatticeBoundForBasis b ty 1 := by
  refine ⟨fun μ => iotaQ_bij S (he μ) (hiso μ) (hs μ), one_pos, fun _ => 1, rfl, fun _ => one_pos,
    Formalism.BasicNotions.DV.rhoUnit_one D, fun μ σ => ?_⟩
  rw [iotaQ_adj S (he μ) (hiso μ) (hs μ)]
  simp [hl]

end Gen

section Rec

variable {R : Ranks} (H : Host R)

variable {W : Type} [Fintype W] (u0 : W) (hcW : W → Tau2 R → HCParam R)
  (hv0 : ∀ u τ, (hcW u τ).v = (hcW u0 τ).v) (hb0 : ∀ u τ, (hcW u τ).b = (hcW u0 τ).b)
  (he0 : ∀ u τ, (hcW u τ).e = (hcW u0 τ).e)
  (hf0 : ∀ u τ (h : 0 < R.k), (hcW u τ).u ⟨0, h⟩ = (hcW u0 τ).u ⟨0, h⟩)
  (hl0 : ∀ u τ (h : 0 < R.k), (hcW u τ).u ⟨R.k - 1, by omega⟩ = (hcW u0 τ).u ⟨R.k - 1, by omega⟩)
  (Del : ℚ) (hDel : 0 < Del)
  (hgap : ∀ u (τ : Tau2 R) (l : ℕ) (h : l + 1 < R.k - 1),
    (hcW u τ).v ⟨l, by omega⟩ - (hcW u τ).v ⟨l + 1, h⟩ = 4 * Del)
  (lt : W → Fin (R.k - 2) → Bool) (hlt : Function.Injective lt)
  (hlet : ∀ u (τ : Tau2 R) (l : ℕ) (h : l < R.k - 2),
    (hcW u τ).u ⟨l + 1, by omega⟩ = (hcW u τ).v ⟨l, by omega⟩ - 1 / 2 - (if lt u ⟨l, h⟩ then Del else 0))
  (cdS : ∀ (n : ℕ) (_ : Fin n → Bool), NNReal) (hcdS : ∀ n ε, 0 < cdS n ε)
  (dsg : Tau2 R → ℝ) (hdsg : ∀ ρ, 0 < dsg ρ) (etaF : ℝ)

variable (hv : W → ℝ) (vol : @HSpace H.E _ _ H.cmStar → ℝ) (hvol : ∀ V, 0 < vol V) (K : W → ClsPkg)
  (T : W → ℕ) [hT : ∀ u, Fact (T u).Prime] (Dst : ℝ) (hD : 0 < Dst) (du : W → ℕ) (hdu : ∀ u, 0 < du u)
  (Gam : ℝ) (hG : 1 < Gam)
  (hwin : ∀ u, (memW hcW K T Dst hD du hdu Gam hG u).A.Tstar ≤ (T u : ℝ) ∧
    (T u : ℝ) ≤ (1 + 1 / ((R.f : ℝ) * R.k)) * (memW hcW K T Dst hD du hdu Gam hG u).A.Tstar)
  (hg : ∀ k, (placesOver H.E (H.g k)).ncard = Module.finrank ℚ H.E) (ht : THyp H)
  (hlev : ∀ u, T u ∈ H.levelPrimes) (hpde : ∀ u, T u ≠ H.pde ∧ T u ≠ H.pde')
  (pz : W → 𝓞 H.E) (hK : ∀ u, (pz u : H.E) ∈ H.K)
  (hpz : ∀ u, (pz u : H.E) * H.conj (pz u : H.E) = (T u : H.E))
  (hcong : ∀ u, (pz u - 1) ∈ Ideal.span {((H.QS * H.q * H.d * (H.g 0 * H.g 1) ^ 2 : ℕ) : 𝓞 H.E)})
  (lat : letI := H.cmStar; ∀ u i, (K u).cls i → Submodule (𝓞 H.E) ((hostSpacesOfNorm H (T u0) (pz u0) (hpz u0)).X i).V)
  (hlat : letI := H.cmStar; ∀ u i c, Submodule.IsLattice H.E (lat u i c))
  (G : LocalGap H)
  (kb : ∀ j, Tau2 R → Fin (R.sigW j).1 → ℤ) (ks : ∀ j, Tau2 R → Fin (R.sigW j).2 → ℤ)
  (tw : (@placesOf H.E _ _ H.cmStar).Pl → Bool)
  (htw : ∀ w, tw ((@placesOf H.E _ _ H.cmStar).conj w) = tw w)

variable (d Dall d0 : ℕ) (hd : d ≤ Dall) (FT : Type) [Fintype FT] [DecidableEq FT]
    (ft : Fin d → FT) (ft0 : Fin d0 → FT)

variable (Lb : Lbl H) (hT2 : ∀ u, T u ≠ 2) (per : ∀ u : W, Bool → FK ((K u).cls R.m) →ₗ[ℂ] En d →ₗ[ℂ] ℂ)
  (NuL : ∀ u : W, Submodule (𝓞 H.E) ((K u).cls 0 → H.E))
  (gat : ∀ (u : W) (w : (@placesOf H.E _ _ H.cmStar).Pl), GIdx H (T u) ((@placesOf H.E _ _ H.cmStar).resChar w) →
    Formalism.MainNotions.G.GAtP ((@placesOf H.E _ _ H.cmStar).resChar w))
  (hgat : ∀ u w h, (gat u w h).d = Fintype.card ((K u).cls 0))

local notation "DR" => (hostLevelRecord H u0 hcW hv0 hb0 he0 hf0 hl0 Del hDel hgap lt hlt hlet cdS hcdS dsg hdsg etaF hv vol hvol K T Dst hD du hdu Gam hG hwin hg ht hlev hpde pz hK hpz hcong lat hlat G kb ks tw htw d Dall d0 hd FT ft ft0 Lb hT2 per NuL gat hgat)

theorem row_sharp_iota (μ) : (RowSide.sharp DR).iota μ = (LinearMap.id : En d →ₗ[ℂ] En d) :=
  (sharp_iota DR μ).trans (rowsN_iota (hd := hd) μ)

theorem row_l1cSharp : SharpLatticeBound DR 1 :=
  latticeBound_one _ _ _ (fun _ => rfl) (fun μ x y => by rw [row_sharp_iota]; rfl)
    (fun μ => by rw [row_sharp_iota]; exact Function.surjective_id) (fun _ _ _ => rfl)

theorem row_l1c0 : (levelRecordBaseSide H u0 hcW hv0 hb0 he0 hf0 hl0 Del hDel hgap lt hlt hlet cdS hcdS dsg hdsg etaF hv vol hvol K T Dst hD du hdu Gam hG hwin hg ht hlev hpde pz hK hpz hcong lat hlat G kb ks tw htw d Dall d0 hd FT ft ft0 Lb hT2 per NuL gat hgat).L1c0 1 :=
  latticeBound_one _ _ _ (fun _ => rfl) (fun μ x y => by rw [show (levelRecordBaseSide H u0 hcW hv0 hb0 he0 hf0 hl0 Del hDel hgap lt hlt hlet cdS hcdS dsg hdsg etaF hv vol hvol K T Dst hD du hdu Gam hG hwin hg ht hlev hpde pz hK hpz hcong lat hlat G kb ks tw htw d Dall d0 hd FT ft ft0 Lb hT2 per NuL gat hgat).s.iota μ = _ from stdSide_iota _ _ _ μ]; rfl)
    (fun μ => by rw [show (levelRecordBaseSide H u0 hcW hv0 hb0 he0 hf0 hl0 Del hDel hgap lt hlt hlet cdS hcdS dsg hdsg etaF hv vol hvol K T Dst hD du hdu Gam hG hwin hg ht hlev hpde pz hK hpz hcong lat hlat G kb ks tw htw d Dall d0 hd FT ft ft0 Lb hT2 per NuL gat hgat).s.iota μ = _ from stdSide_iota _ _ _ μ]; exact Function.surjective_id)
    (fun _ _ _ => rfl)

theorem row_isotRank : Rows.IsotRank (DR).what₂ := by
  intro j _ _ (π : FT)
  show Module.finrank ℂ (Submodule.span ℂ (eb d0 '' {σ | ft0 σ = π})) = Fintype.card {σ : Fin d0 // ft0 σ = π}
  have h : (eb d0 '' {σ | ft0 σ = π}) = Set.range (fun σ : {σ : Fin d0 // ft0 σ = π} => eb d0 σ) := by
    ext x; simp [Set.mem_image]
  rw [h]
  exact finrank_span_eq_card (b := fun σ : {σ : Fin d0 // ft0 σ = π} => eb d0 σ)
    ((eb d0).orthonormal.linearIndependent.comp _ Subtype.val_injective)

theorem row_thetaRat : Idx.ThetaRat (levelRecordDivisor H u0 hcW hv0 hb0 he0 hf0 hl0 Del hDel hgap lt hlt hlet cdS hcdS dsg hdsg etaF hv vol hvol K T Dst hD du hdu Gam hG hwin hg ht hlev hpde pz hK hpz hcong lat hlat G kb ks tw htw d Dall d0 hd FT ft ft0 Lb hT2 per NuL gat hgat) := fun _ _ _ _ x => ⟨x, rfl⟩

theorem row_hermRat : Idx.HermRat DR := fun μ j _ _ (x y : Fin d0 → H.E) => by
  letI : StarRing H.E := H.cmStar
  have e : H.φ₀ (∑ i, star (x i) * y i : H.E) = inner ℂ (jB H.φ₀ (eb d0) x) (jB H.φ₀ (eb d0) y) := by
    rw [inner_jB, map_sum]
    exact Finset.sum_congr rfl fun i _ => by rw [map_mul, emb_star H H.φ₀]
  exact ⟨_, e⟩

theorem stdH_rank (K : Type) [Field K] [NumberField K] [StarRing K] (n : ℕ) : (stdH K n).rank = n := by
  show Module.finrank K (Submodule.span K ((stdH K n).L : Set (stdH K n).V)) = n
  rw [stdH_span, finrank_top]
  exact Module.finrank_fin_fun K

theorem row_rrRank : (DR).div.RR.rank = d :=
  letI : StarRing H.E := H.cmStar
  stdH_rank H.E d

theorem row_mjRank : DV.MjRank DR (levelRecordDivisor H u0 hcW hv0 hb0 he0 hf0 hl0 Del hDel hgap lt hlt hlet cdS hcdS dsg hdsg etaF hv vol hvol K T Dst hD du hdu Gam hG hwin hg ht hlev hpde pz hK hpz hcong lat hlat G kb ks tw htw d Dall d0 hd FT ft ft0 Lb hT2 per NuL gat hgat) := fun _ _ _ =>
  letI : StarRing H.E := H.cmStar
  stdH_rank H.E d0

theorem row_lemma3 (C : ℝ) (hC : 0 ≤ C)
    (hn : ∀ π : FT, Fintype.card {σ : Fin d // ft σ = π} =
      (H.g 0 * H.g 1) ^ (R.f * R.k) * Fintype.card {σ : Fin d0 // ft0 σ = π})
    (h0 : ∀ π : FT, 0 < Fintype.card {σ : Fin d0 // ft0 σ = π}) : Lemma3 DR C := by
  refine ⟨fun _ => (H.g 0 * H.g 1) ^ (R.f * R.k), hn, h0, fun _ _ _ => rfl, fun π => ?_⟩
  have e : (((H.g 0 * H.g 1) ^ (R.f * R.k) : ℕ) : ℝ) - ((H.g 0 * H.g 1 : ℕ) : ℝ) ^ (R.f * R.k) = 0 := by
    push_cast; ring
  show |(((H.g 0 * H.g 1) ^ (R.f * R.k) : ℕ) : ℝ) - ((H.g 0 * H.g 1 : ℕ) : ℝ) ^ (R.f * R.k)| ≤ _
  rw [e, abs_zero]
  positivity

omit kb ks in

theorem row_kapDef : ∃ kb ks, DV.KapDef (hostLevelRecord H u0 hcW hv0 hb0 he0 hf0 hl0 Del hDel hgap lt hlt hlet cdS hcdS dsg hdsg etaF hv vol hvol K T Dst hD du hdu Gam hG hwin hg ht hlev hpde pz hK hpz hcong lat hlat G kb ks tw htw d Dall d0 hd FT ft ft0 Lb hT2 per NuL gat hgat) := by
  obtain ⟨kb, ks, h⟩ := DV.exists_blocks (hostLevelRecord H u0 hcW hv0 hb0 he0 hf0 hl0 Del hDel hgap lt hlt hlet cdS hcdS dsg hdsg etaF hv vol hvol K T Dst hD du hdu Gam hG hwin hg ht hlev hpde pz hK hpz hcong lat hlat G (fun _ _ _ => 0) (fun _ _ _ => 0) tw htw d Dall d0 hd FT ft ft0 Lb hT2 per NuL gat hgat)
  exact ⟨kb, ks, fun j _ _ τ => h j τ⟩

end Rec

end Formalism.BasicNotions.Examples₂.NZ
