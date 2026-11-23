import Development.EtaleCohomology.TateTwists.CupflipAwFlipPf

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

noncomputable section
namespace LateralTheory.EtaleFoundations

def phiT {R : Type} [CommRing R] {I J K : Cx R} (μ : Pair I J K) {E : Spc} {n m k : ℤ} (hk : n + m = k)
    (α : Cochain ((chains R).obj E) I n) (β : Cochain ((chains R).obj E) J m) {N : ℕ} {U : Scheme.{0}}
    (x : Sx E N U) (w : ℤ) (z : Pr N) : Sec (K.X w) U :=
  if h : -((z.1 : ℤ) + (z.2.1 : ℤ)) + k = w then
    ((m * (z.1 : ℤ)).negOnePow : ℤ) • μ.mul U (-(z.1 : ℤ) + n) (-(z.2.1 : ℤ) + m) w (by omega)
      (ev α z.1 _ rfl U (x.along z.2.2.1)) (ev β z.2.1 _ rfl U (x.along z.2.2.2))
  else 0

def phi {R : Type} [CommRing R] {I J K : Cx R} (μ : Pair I J K) {E : Spc} {n m k : ℤ} (hk : n + m = k)
    (α : Cochain ((chains R).obj E) I n) (β : Cochain ((chains R).obj E) J m) {N : ℕ} {U : Scheme.{0}}
    (x : Sx E N U) (w : ℤ) (c : Pr N →₀ ℤ) : Sec (K.X w) U :=
  c.sum fun z a => a • phiT μ hk α β x w z

theorem ev_sub' {R : Type} [CommRing R] {E : Spc} {I : Cx R} {n : ℤ} (α β : Cochain ((chains R).obj E) I n) p s h U x :
    ev (α - β) p s h U x = ev α p s h U x - ev β p s h U x := by
  simp [ev, Cochain.sub_v, Preadditive.comp_sub]
  rfl

theorem ev_zsmul' {R : Type} [CommRing R] {E : Spc} {I : Cx R} {n : ℤ} (α : Cochain ((chains R).obj E) I n) p s h U x
    (c : ℤ) : ev (c • α) p s h U x = c • ev α p s h U x := by
  simp [ev, Cochain.smul_v, Linear.comp_smul]
  rfl

def cupflip_ev_ext : Prop :=
  ∀ (R : Type) [CommRing R] {E : Spc} {I : Cx R} {n : ℤ},
    ∀ α β : Cochain ((chains R).obj E) I n, (∀ p s h U x, ev α p s h U x = ev β p s h U x) → α = β

def cupflip_eta_mk : Prop :=
  ∀ h : ∀ N, Pr N →₀ ℤ, (∀ N, Pr.Deg (N + 1) (h N)) →
  ∀ (R : Type) [CommRing R] {I J K : Cx R} (μ : Pair I J K) (E : Spc) {n m k : ℤ} (hk : n + m = k)
    (α : Cochain ((chains R).obj E) I n) (β : Cochain ((chains R).obj E) J m),
    ∃ η : Cochain ((chains R).obj E) K (k - 1), ∀ N s hs U x, ev η N s hs U x = phi μ hk α β x s (h N)

def cupflip_eta_delta : Prop :=
  ∀ h : ∀ N, Pr N →₀ ℤ, CupflipSteen h →
  ∀ (R : Type) [CommRing R] {I J K : Cx R} (μ : Pair I J K) (E : Spc) {n m k : ℤ} (hk : n + m = k)
    (α : Cocycle ((chains R).obj E) I n) (β : Cocycle ((chains R).obj E) J m)
    (η : Cochain ((chains R).obj E) K (k - 1)),
    (∀ N s hs U x, ev η N s hs U x = phi μ hk α.1 β.1 x s (h N)) →
    ∀ N t ht U x, ev (δ (k - 1) k η) N t ht U x =
      (k.negOnePow : ℤ) • (phi μ hk α.1 β.1 x t (Pr.aw N) - phi μ hk α.1 β.1 x t (Pr.wa N))

theorem phi_aw {R : Type} [CommRing R] {I J K : Cx R} (μ : Pair I J K) {E : Spc} {n m k : ℤ} (hk : n + m = k)
    (α : Cochain ((chains R).obj E) I n) (β : Cochain ((chains R).obj E) J m) (γ : Cochain ((chains R).obj E) K k)
    (hγ : μ.IsAW hk α β γ) (N : ℕ) (t : ℤ) (ht : -(N : ℤ) + k = t) (U : Scheme.{0}) (x : Sx E N U) :
    phi μ hk α β x t (Pr.aw N) = ev γ N t ht U x := by
  rw [hγ N t ht U x, phi, Pr.aw, ← Finsupp.sum_finsetSum_index (fun z => zero_smul ℤ (phiT μ hk α β x t z))
    (fun z a b => add_smul a b (phiT μ hk α β x t z))]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [Finsupp.sum_single_index (zero_smul ℤ (phiT μ hk α β x t _)), one_smul, phiT, dif_pos (by have := p.2; push_cast [Nat.cast_sub (by omega : (p : ℕ) ≤ N)]; omega)]
  rw [Units.smul_def]
  rfl

def cupflip_phi_diag : Prop :=
  ∀ (R : Type) [CommRing R] {I J K : Cx R} (μ : Pair I J K) (ν : Pair J I K), μ.IsFlip ν →
    ∀ (E : Spc) {n m k : ℤ} (hk : n + m = k) (hk' : m + n = k)
      (α : Cochain ((chains R).obj E) I n) (β : Cochain ((chains R).obj E) J m)
      (γ' : Cochain ((chains R).obj E) K k), ν.IsAW hk' β α γ' →
      ∀ (N : ℕ) (t : ℤ) (ht : -(N : ℤ) + k = t) (U : Scheme.{0}) (x : Sx E N U),
        phi μ hk α β x t (Pr.wa N) = ((n * m).negOnePow : ℤ) • ev γ' N t ht U x

theorem cupflip_phi_diag_pf : cupflip_phi_diag := by
  intro R _ I J K μ ν hflip E n m k hk hk' α β γ' hγ' N t ht U x
  rw [hγ' N t ht U x, phi, Pr.wa, ← Finsupp.sum_finsetSum_index (fun z => zero_smul ℤ (phiT μ hk α β x t z))
    (fun z a b => add_smul a b (phiT μ hk α β x t z)), Finset.smul_sum]
  refine Finset.sum_congr rfl fun p _ => ?_
  have hp := p.2
  rw [Finsupp.sum_single_index (zero_smul ℤ (phiT μ hk α β x t _)), phiT,
    dif_pos (by push_cast [Nat.cast_sub (by omega : (p : ℕ) ≤ N)]; omega)]
  rw [hflip U _ _ t (by push_cast [Nat.cast_sub (by omega : (p : ℕ) ≤ N)]; omega)]
  simp only [Units.smul_def, smul_smul]
  congr 1
  have e : ((-1 : ℤ) ^ ((p : ℕ) * (N - p))) = (((p : ℕ) : ℤ) * ((N - p : ℕ) : ℤ)).negOnePow := by
    rw [Int.negOnePow_def, ← Nat.cast_mul, zpow_natCast]; simp
  rw [e]
  simp only [← Units.val_mul, ← Int.negOnePow_add]
  congr 1
  rw [Int.negOnePow_eq_iff]
  exact ⟨m * ((N - p : ℕ) : ℤ) - n * m, by ring⟩

theorem cupflip_homotopy_of (hext : cupflip_ev_ext) (hmk : cupflip_eta_mk) (hdl : cupflip_eta_delta) :
    cupflip_homotopy := by
  intro h hs R _ I J K μ ν hflip E n m k hk hk' α β γ γ' hγ hγ'
  obtain ⟨η, hη⟩ := hmk h hs.1 R μ E hk α.1 β.1
  have hd := hdl h hs R μ E hk α β η hη
  refine ⟨((k.negOnePow : ℤˣ) : ℤ) • η, ?_⟩
  rw [show δ (k - 1) k (((k.negOnePow : ℤˣ) : ℤ) • η) = ((k.negOnePow : ℤˣ) : ℤ) • δ (k - 1) k η from
    (δ_hom ℤ _ _ (k - 1) k).map_smul _ _]
  apply hext R
  intro N t ht U x
  have h1 := phi_aw μ hk α.1 β.1 γ.1 hγ N t ht U x
  have h2 := cupflip_phi_diag_pf R μ ν hflip E hk hk' α.1 β.1 γ'.1 hγ' N t ht U x
  rw [ev_zsmul', hd N t ht U x, h1, h2, smul_smul, ← Units.val_mul,
    Int.units_mul_self, Units.val_one, one_smul, Units.smul_def, ev_sub', ev_zsmul']

end LateralTheory.EtaleFoundations
