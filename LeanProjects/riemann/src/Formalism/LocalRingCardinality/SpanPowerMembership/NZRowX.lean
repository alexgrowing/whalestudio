import Formalism.LocalRingCardinality.SpanPowerMembership.NZRowW
import Formalism.LocalRingCardinality.SpanPowerMembership.NZColG

noncomputable section

namespace Formalism.BasicNotions.Examples₂.NZ

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.Examples₂

section Gen

variable (D : D7)

theorem nprime_of (L : SizeData₂ D) (hs : L.supp = ∅) (hN : ∀ u, L.NuLat u = (D.div.Nu u).L) : DV.NprimeDef D L := by
  intro u
  have hI : DV.Iu D L u = 1 := by
    unfold DV.Iu
    rw [hs, Finset.prod_empty]
  rw [hI, ← hN u]
  apply le_antisymm
  · intro y hy
    exact Submodule.subset_span ⟨1, FractionalIdeal.one_mem_one _, y, hy, (one_smul _ _).symm⟩
  · rw [Submodule.span_le]
    rintro x ⟨a, ha, y, hy, rfl⟩
    obtain ⟨r, rfl⟩ := (FractionalIdeal.mem_one_iff _).mp ha
    rw [algebraMap_smul]
    exact Submodule.smul_mem _ _ hy

theorem lenLoc_self {V : Type} [AddCommGroup V] [Module (𝓞 D.what₂.LL) V] (w : HeightOneSpectrum (𝓞 D.what₂.LL))
    (A : Submodule (𝓞 D.what₂.LL) V) : DV.lenLoc w A A = 0 := by
  unfold DV.lenLoc
  have : Subsingleton (↥A ⧸ A.comap A.subtype) := by
    rw [Submodule.comap_subtype_self]
    exact not_nontrivial_iff_subsingleton.mp fun hnt => Submodule.Quotient.nontrivial_iff.mp hnt rfl
  rw [Module.length_eq_zero]

theorem locLe_self (w : HeightOneSpectrum (𝓞 D.what₂.LL)) {V : Type} [AddCommGroup V] [Module (𝓞 D.what₂.LL) V]
    (A : Submodule (𝓞 D.what₂.LL) V) : DV.LocLe w 0 A A := fun x hx =>
  ⟨1, fun h => w.isPrime.ne_top ((Ideal.eq_top_iff_one _).mpr h), by rw [pow_zero, Ideal.one_eq_top, Submodule.top_smul, one_smul]; exact hx⟩

theorem nuDef_of (L : SizeData₂ D) (hN : ∀ u, L.NuLat u = DV.MramL D u) (hlen : ∀ u w, L.lenMN u w = 0) : DV.NuDef D L := by
  refine ⟨fun u w _ => ?_, fun u w _ _ => ?_, fun u w l hl => ?_⟩
  · rw [hN]; exact locLe_self D _ _
  · rw [hN]; exact ⟨locLe_self D _ _, locLe_self D _ _⟩
  · rw [hN, lenLoc_self] at hl
    rw [hlen]
    have : l = 0 := by exact_mod_cast hl.symm
    simp [this]

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

theorem row_mramL (hN : ∀ u, NuL u = (stdHLat H.E ((K u).cls 0)).L) (u : W) : DV.MramL DR u = ((DR).div.Nu u).L := by
  show (stdHLat H.E ((K u).cls 0)).L.comap ((LinearMap.id : ((K u).cls 0 → H.E) →ₗ[H.E] _).restrictScalars _) = NuL u
  rw [hN u]
  ext x
  rfl

def levelRecordParameters (L : SizeData₂ DR) : SizeData₂ DR := withNu L (fun u => ((DR).div.Nu u).L) (fun _ _ => 0)

theorem row_nprime (L : SizeData₂ DR) (hs : L.supp = ∅) : DV.NprimeDef DR (levelRecordParameters H u0 hcW hv0 hb0 he0 hf0 hl0 Del hDel hgap lt hlt hlet cdS hcdS dsg hdsg etaF hv vol hvol K T Dst hD du hdu Gam hG hwin hg ht hlev hpde pz hK hpz hcong lat hlat G kb ks tw htw d Dall d0 hd FT ft ft0 Lb hT2 per NuL gat hgat L) :=
  nprime_of DR _ hs fun _ => rfl

theorem row_nuDef (hN : ∀ u, NuL u = (stdHLat H.E ((K u).cls 0)).L) (L : SizeData₂ DR) : DV.NuDef DR (levelRecordParameters H u0 hcW hv0 hb0 he0 hf0 hl0 Del hDel hgap lt hlt hlet cdS hcdS dsg hdsg etaF hv vol hvol K T Dst hD du hdu Gam hG hwin hg ht hlev hpde pz hK hpz hcong lat hlat G kb ks tw htw d Dall d0 hd FT ft ft0 Lb hT2 per NuL gat hgat L) :=
  nuDef_of DR _ (fun u => (row_mramL H u0 hcW hv0 hb0 he0 hf0 hl0 Del hDel hgap lt hlt hlet cdS hcdS dsg hdsg etaF hv vol hvol K T Dst hD du hdu Gam hG hwin hg ht hlev hpde pz hK hpz hcong lat hlat G kb ks tw htw d Dall d0 hd FT ft ft0 Lb hT2 per NuL gat hgat hN u).symm) fun _ _ => rfl

end Rec

end Formalism.BasicNotions.Examples₂.NZ
