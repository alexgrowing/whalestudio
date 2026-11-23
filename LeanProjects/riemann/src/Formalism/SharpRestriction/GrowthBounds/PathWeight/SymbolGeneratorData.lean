import Formalism.SharpRestriction.GrowthBounds.PathWeight.PhProdShift

noncomputable section

open MvPolynomial Finset Classical

namespace Formalism.MainNotions.G.symbolGeneratorData

open Formalism.MainNotions.G Formalism.MainNotions.SourceCleaning Formalism.MainNotions.G.WittFrameLocaliserOrders

theorem ph_det_pow (R : Type) [CommRing R] (p : ℕ) [Fact p.Prime] (e : ℕ) {n : ℕ} (M : Matrix (Fin n) (Fin n) R) :
    ∃ h : R, (M.map (· ^ p ^ e)).det = M.det ^ (p ^ e) + (p : R) * h := by
  let MU : Matrix (Fin n) (Fin n) (MvPolynomial (Fin n × Fin n) ℤ) := Matrix.of fun i j => X (i, j)
  have hdvd : C ((p : ℕ) : ℤ) ∣ (MU.map (· ^ p ^ e)).det - MU.det ^ (p ^ e) := by
    rw [MvPolynomial.C_dvd_iff_zmod]
    rw [map_sub, map_pow, RingHom.map_det, RingHom.map_det, sub_eq_zero]
    have h1 := RingHom.map_det (iterateFrobenius (MvPolynomial (Fin n × Fin n) (ZMod p)) p e)
      ((MvPolynomial.map (Int.castRingHom (ZMod p))).mapMatrix MU)
    rw [iterateFrobenius_def] at h1
    rw [h1]
    congr 1
    ext i j
    simp [iterateFrobenius_def]
  obtain ⟨h, hh⟩ := hdvd
  let ψ : MvPolynomial (Fin n × Fin n) ℤ →+* R := MvPolynomial.eval₂Hom (Int.castRingHom R) fun ij => M ij.1 ij.2
  refine ⟨ψ h, ?_⟩
  have h2 := congrArg ψ hh
  rw [map_sub, map_pow, RingHom.map_det, RingHom.map_det, map_mul] at h2
  have e1 : ψ.mapMatrix (MU.map (· ^ p ^ e)) = M.map (· ^ p ^ e) := by
    ext i j; simp [ψ, MU]
  have e2 : ψ.mapMatrix MU = M := by
    ext i j; simp [ψ, MU]
  have e3 : ψ (C ((p : ℕ) : ℤ)) = (p : R) := by simp [ψ]
  rw [e1, e2, e3] at h2
  rw [← h2]; ring

section Sub

variable {A : Type} [CommRing A] {O : Type} [CommRing O] [Algebra O A] (S : Subalgebra O A)

theorem ph_det_pow_sub (p : ℕ) [Fact p.Prime] (e : ℕ) {n : ℕ} (M : Matrix (Fin n) (Fin n) A) (hM : ∀ i j, M i j ∈ S) :
    ∃ h ∈ S, (M.map (· ^ p ^ e)).det = M.det ^ (p ^ e) + (p : A) * h := by
  let M' : Matrix (Fin n) (Fin n) S := Matrix.of fun i j => ⟨M i j, hM i j⟩
  obtain ⟨h, hh⟩ := ph_det_pow S p e M'
  refine ⟨h.1, h.2, ?_⟩
  have h2 := congrArg S.val hh
  rw [AlgHom.map_det, map_add, map_pow, AlgHom.map_det, map_mul, map_natCast] at h2
  have e1 : S.val.mapMatrix (M'.map (· ^ p ^ e)) = M.map (· ^ p ^ e) := by
    ext i j; simp [M']
  have e2 : S.val.mapMatrix M' = M := by
    ext i j; simp [M']
  rw [e1, e2] at h2
  exact h2

def Spl (π a f : A) : Prop := ∃ H ∈ S, ∃ Y ∈ S, f = a * H + π * Y

theorem Spl_pow (π D h : A) (hπ : π ∈ S) (hD : D ∈ S) (hh : h ∈ S) (P n c : ℕ) (hP : 1 ≤ P) :
    Spl S (π ^ c) (D ^ (n - c)) ((D ^ P + π * h) ^ n) := by
  have := Formalism.CountingSumsFrames.Top.powerSplit S ⟨D, hD⟩ ⟨h, hh⟩ ⟨π, hπ⟩ P n c hP
  obtain ⟨y, hy, z, hz, hyz⟩ := Submodule.mem_sup.1 this
  obtain ⟨a, rfl⟩ := Ideal.mem_span_singleton'.1 hy
  obtain ⟨b, rfl⟩ := Ideal.mem_span_singleton'.1 hz
  refine ⟨a.1, a.2, b.1, b.2, ?_⟩
  have h2 := congrArg S.val hyz
  simp only [map_add, map_mul, map_pow, Subalgebra.coe_val] at h2
  rw [← h2]; ring

theorem Spl_one (π : A) : Spl S π 1 1 := ⟨1, one_mem _, 0, zero_mem _, by simp⟩

theorem Spl_mul {π a b f g : A} (hπ : π ∈ S) (ha : a ∈ S) (hb : b ∈ S) (hf : Spl S π a f) (hg : Spl S π b g) :
    Spl S π (a * b) (f * g) := by
  obtain ⟨H1, h1, Y1, y1, rfl⟩ := hf
  obtain ⟨H2, h2, Y2, y2, rfl⟩ := hg
  refine ⟨H1 * H2, mul_mem h1 h2, a * H1 * Y2 + Y1 * (b * H2) + π * Y1 * Y2, ?_, by ring⟩
  exact add_mem (add_mem (mul_mem (mul_mem ha h1) y2) (mul_mem y1 (mul_mem hb h2))) (mul_mem (mul_mem hπ y1) y2)

theorem Spl_prod {κ : Type*} {π : A} (hπ : π ∈ S) (s : Finset κ) (a f : κ → A) (ha : ∀ t ∈ s, a t ∈ S)
    (h : ∀ t ∈ s, Spl S π (a t) (f t)) : Spl S π (∏ t ∈ s, a t) (∏ t ∈ s, f t) := by
  induction s using Finset.induction_on with
  | empty => simpa using Spl_one S π
  | insert x s hx ih =>
    rw [Finset.prod_insert hx, Finset.prod_insert hx]
    exact Spl_mul S hπ (ha x (Finset.mem_insert_self x s))
      (prod_mem fun t ht => ha t (Finset.mem_insert_of_mem ht)) (h x (Finset.mem_insert_self x s))
      (ih (fun t ht => ha t (Finset.mem_insert_of_mem ht)) fun t ht => h t (Finset.mem_insert_of_mem ht))

end Sub

section Conc

variable {p n' r K : ℕ} [Fact p.Prime] [NeZero n'] [NeZero r] [NeZero K] {O : Type} [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] [Algebra (WF p n') O] (X : Ctx p n' r K O)

local notation "AA" => MvPolynomial (TV n' (r + K)) O
local notation "PP" => MvPolynomial (TV n' (r + K)) (KK O)

def Ctx.SS : Subalgebra O AA := supported O (bc_St X.Fr (r + K))

def Ctx.DsO (s : ℤ) : AA := (topPairingMatrix p O X.Fr X.hH.2.2.1 s).det

def Ctx.DlM (j : ℤ) : Matrix (Fin r) (Fin r) AA :=
  Matrix.of fun l b : Fin r => MvPolynomial.X (posOf n' (X.Fr.fr j l.val), Fin.castAdd K b) ^ (p ^ (zF X.Fr j - X.Fr.fr j l.val).toNat)

def Ctx.DlO (j : ℤ) : AA := (X.DlM j).det

theorem ph_hr (Z : Ctx p n' r K O) : 1 ≤ r := by have := Z.hH.2.1; omega

theorem ph_T_mem (s : ℤ) (l i : Fin r) : topPairingMatrix p O X.Fr X.hH.2.2.1 s l i ∈ X.SS := by
  have hA := window_holds_even_tops n' r X.Fr X.L₁ X.N₁ X.hV X.hH.2.2.2.2 (ph_hr X) s
  refine row_power_mem_supported X.Fr X.hH.2.2.1 s _ (fun l i => ?_) l i
  have hE := (posOf_even X.hH.2.2.2.2 _).2 (hA l.val l.2).1
  refine ⟨?_, (hA l.val l.2).2.1⟩
  rw [normal_variable_iff_even_index hE]
  have := i.2
  simp only [Fin.val_castLE]
  omega

theorem ph_DsO_mem (s : ℤ) : X.DsO s ∈ X.SS := det_mem_subalgebra_alt _ _ (ph_T_mem X s)

theorem ph_DsO_map (s : ℤ) : MvPolynomial.map (algebraMap O (KK O)) (X.DsO s) =
    X.sb (Dtop p n' O X.Fr X.hH.2.2.1 X.g s) :=
  (subst_top_determinant X.S.w X.Fr X.hH.2.2.1 X.hg X.hH.2.2.2.2 s
    (window_holds_even_tops n' r X.Fr X.L₁ X.N₁ X.hV X.hH.2.2.2.2 (ph_hr X) s)).symm

theorem ph_DlM_mem (j : ℤ) (l b : Fin r) : X.DlM j l b ∈ X.SS := by
  refine (supported O (bc_St X.Fr (r + K))).pow_mem (X_mem_supported.mpr ?_) _
  have hE := (posOf_even X.hH.2.2.2.2 (X.Fr.fr j l.val)).2 (X.hV.2.2.2.2.1 j l.val l.2).2
  refine ⟨?_, (X.hV.2.2.2.2.1 j l.val l.2).1⟩
  rw [normal_variable_iff_even_index hE]
  have := b.2
  simp only [Fin.val_castAdd]
  omega

theorem ph_DlO_mem (j : ℤ) : X.DlO j ∈ X.SS := det_mem_subalgebra_alt _ _ (ph_DlM_mem X j)

theorem ph_Ifirst (i : Fin r) :
    (Ifirst r (r + K)).orderEmbOfFin (first_columns_card X.hH.2.2.1) i = Fin.castLE X.hH.2.2.1 i := by
  have := Finset.orderEmbOfFin_unique (first_columns_card X.hH.2.2.1) (f := Fin.castLE X.hH.2.2.1)
    (fun x => by simp [Ifirst]) (fun a b h => by simpa using h)
  exact (congrFun this i).symm

theorem ph_DlO_map (j : ℤ) : MvPolynomial.map (algebraMap O (KK O)) (X.DlO j) = X.sb (Del p n' O X.Fr X.g j) := by
  unfold Ctx.DlO Del minorI Ctx.sb
  rw [dif_pos (first_columns_card X.hH.2.2.1), AlgHom.map_det, RingHom.map_det]
  refine congrArg Matrix.det (Matrix.ext fun l i => ?_)
  show MvPolynomial.map (algebraMap O (KK O)) (X.DlM j l i) = subst p n' O X.S.w n' r X.g
    (twRow p n' O X.Fr X.g j l.val ((Ifirst r (r + K)).orderEmbOfFin (first_columns_card X.hH.2.2.1) i))
  unfold twRow
  rw [ph_Ifirst X, map_pow, substitute_primal_top_variable X.S.w X.hH.2.2.1 X.hg X.hH.2.2.2.2 _ (X.hV.2.2.2.2.1 j l.val l.2).2]
  simp only [Ctx.DlM, Matrix.of_apply, map_pow, MvPolynomial.map_X]
  rfl

theorem ph_DlO_period (j : ℤ) : X.DlO (j + X.Fr.J) = X.DlO j := by
  unfold Ctx.DlO
  refine congrArg Matrix.det (Matrix.ext fun l i => ?_)
  simp only [Ctx.DlM, Matrix.of_apply, zF]
  rw [X.hV.2.1 j l.val, X.hV.2.1 j (r - 1), bf_posOf_add]
  congr 3
  ring

theorem ph_Dseg (j x : ℤ) (hx : x ∈ nonW X.Fr j) :
    ∃ h ∈ X.SS, phSeg O K p X.Fr j (Dseg X.Fr O K x) =
      X.DsO ((posOf n' x).val : ℤ) ^ (p ^ (zF X.Fr j - x).toNat) + (p : AA) * h := by
  obtain ⟨h, hh, he⟩ := ph_det_pow_sub X.SS p (zF X.Fr j - x).toNat
    (topPairingMatrix p O X.Fr X.hH.2.2.1 ((posOf n' x).val : ℤ)) (ph_T_mem X _)
  refine ⟨h, hh, ?_⟩
  rw [Ctx.DsO, ← he]
  unfold Dseg
  rw [AlgHom.map_det]
  refine congrArg Matrix.det (Matrix.ext fun l i => ?_)
  have hA := window_holds_even_tops n' r X.Fr X.L₁ X.N₁ X.hV X.hH.2.2.2.2 (ph_hr X) x l.val l.2
  have hxz : x ≤ zF X.Fr j := by
    have := (Finset.mem_filter.1 (Finset.mem_filter.1 hx).1).1
    exact (Finset.mem_Icc.1 this).2
  have hs : x = ((posOf n' x).val : ℤ) + n' * (x / n') := by
    rw [posOf_val]; exact (Int.emod_add_mul_ediv x n').symm
  have hAr : Arow X.Fr x l.val = Arow X.Fr ((posOf n' x).val : ℤ) l.val + n' * (x / n') := by
    conv_lhs => rw [hs]
    exact ph_Arow_shift X.Fr X.hV X.hH.2.2.2.2 (ph_hr X) _ _ _ l.2
  show phSeg O K p X.Fr j (MvPolynomial.X (Arow X.Fr x l.val, Fin.castAdd K i)) =
    (MvPolynomial.X (posOf n' (Arow X.Fr ((posOf n' x).val : ℤ) l.val), Fin.castLE X.hH.2.2.1 i) ^
      rowPowerExponent p X.Fr ((posOf n' x).val : ℤ) l.val) ^ p ^ (zF X.Fr j - x).toNat
  unfold phSeg rowPowerExponent
  rw [aeval_X, ← pow_mul, ← pow_add]
  have e1 : posOf n' (Arow X.Fr x l.val) = posOf n' (Arow X.Fr ((posOf n' x).val : ℤ) l.val) := by
    rw [hAr, posOf_add_mul_alt]
  have e2 : X.Fr.dist j (Arow X.Fr x l.val) =
      (((posOf n' x).val : ℤ) - Arow X.Fr ((posOf n' x).val : ℤ) l.val).toNat + (zF X.Fr j - x).toNat := by
    unfold Frames.dist
    unfold zF at hxz ⊢
    have := hA.2.2
    omega
  simp only [e1, e2]
  rfl

theorem ph_Wseg (j : ℤ) :
    ∃ h ∈ X.SS, phSeg O K p X.Fr j (Wseg X.Fr j O K) = X.DlO (j - 1) ^ (Qj X.Fr p (j - 1)) + (p : AA) * h := by
  obtain ⟨h, hh, he⟩ := ph_det_pow_sub X.SS p (zF X.Fr j - zF X.Fr (j - 1)).toNat (X.DlM (j - 1)) (ph_DlM_mem X _)
  refine ⟨h, hh, ?_⟩
  have hQ : Qj X.Fr p (j - 1) = p ^ (zF X.Fr j - zF X.Fr (j - 1)).toNat := by
    unfold Qj; rw [sub_add_cancel]
  rw [hQ, Ctx.DlO, ← he]
  unfold Wseg
  rw [AlgHom.map_det]
  refine congrArg Matrix.det (Matrix.ext fun l i => ?_)
  show phSeg O K p X.Fr j (MvPolynomial.X (X.Fr.fr (j - 1) l.val, Fin.castAdd K i)) =
    (MvPolynomial.X (posOf n' (X.Fr.fr (j - 1) l.val), Fin.castAdd K i) ^
      (p ^ (zF X.Fr (j - 1) - X.Fr.fr (j - 1) l.val).toNat)) ^ p ^ (zF X.Fr j - zF X.Fr (j - 1)).toNat
  unfold phSeg
  rw [aeval_X, ← pow_mul, ← pow_add]
  have h1 := frame_entry_le_last X.Fr X.L₁ X.N₁ X.hV (j - 1) l.val l.2
  have h2 := X.hV.2.2.2.1 (j - 1)
  rw [sub_add_cancel] at h2
  have h3 := frame_row_monotone X.Fr X.L₁ X.N₁ X.hV j (r - 1) (by have := ph_hr X; omega)
  have e2 : X.Fr.dist j (X.Fr.fr (j - 1) l.val) =
      (zF X.Fr (j - 1) - X.Fr.fr (j - 1) l.val).toNat + (zF X.Fr j - zF X.Fr (j - 1)).toNat := by
    unfold Frames.dist zF
    omega
  simp only [e2]

end Conc

theorem restPh : RestPh := by
  intro p n' r K _ _ _ _ O _ _ _ _ X c'
  have hr := ph_hr X
  have hp : 0 < p := (Fact.out : p.Prime).pos
  have hπ : (p : MvPolynomial (TV n' (r + K)) O) ∈ X.SS := natCast_mem _ _
  have hπc : (p : MvPolynomial (TV n' (r + K)) O) ^ c' ∈ X.SS := pow_mem hπ _
  have hD : ∀ (j x : ℤ), x ∈ nonW X.Fr j → Spl X.SS ((p : MvPolynomial (TV n' (r + K)) O) ^ c')
      (X.DsO ((posOf n' x).val : ℤ) ^ (X.m1 c' - c')) ((phSeg O K p X.Fr j (Dseg X.Fr O K x)) ^ (X.m1 c')) := by
    intro j x hx
    obtain ⟨h, hh, he⟩ := ph_Dseg X j x hx
    rw [he]
    exact Spl_pow X.SS _ _ h hπ (ph_DsO_mem X _) hh _ _ c' (Nat.one_le_pow _ _ hp)
  have hW : ∀ j : ℤ, Spl X.SS ((p : MvPolynomial (TV n' (r + K)) O) ^ c')
      (X.DlO (j - 1) ^ (X.m2 c' - c')) ((phSeg O K p X.Fr j (Wseg X.Fr j O K)) ^ (X.m2 c')) := by
    intro j
    obtain ⟨h, hh, he⟩ := ph_Wseg X j
    rw [he]
    exact Spl_pow X.SS _ _ h hπ (ph_DlO_mem X _) hh _ _ c' (Nat.one_le_pow _ _ hp)
  have hj : ∀ j ∈ Finset.range X.Fr.J, Spl X.SS ((p : MvPolynomial (TV n' (r + K)) O) ^ c')
      ((∏ x ∈ nonW X.Fr (j : ℤ), X.DsO ((posOf n' x).val : ℤ) ^ (X.m1 c' - c')) *
        X.DlO ((j : ℤ) - 1) ^ (X.m2 c' - c'))
      (phSeg O K p X.Fr (j : ℤ) (Dv X.Fr (j : ℤ) O K (X.m1 c') (X.m2 c'))) := by
    intro j _
    unfold Dv
    rw [map_mul, map_prod, map_pow]
    simp only [map_pow]
    exact Spl_mul X.SS hπc (prod_mem fun x _ => pow_mem (ph_DsO_mem X _) _) (pow_mem (ph_DlO_mem X _) _)
      (Spl_prod X.SS hπc _ _ _ (fun x _ => pow_mem (ph_DsO_mem X _) _) (fun x hx => hD j x hx)) (hW j)
  obtain ⟨H0, hH0, Y0, hY0, he⟩ := Spl_prod X.SS hπc (Finset.range X.Fr.J) _ _
    (fun j _ => mul_mem (prod_mem fun x _ => pow_mem (ph_DsO_mem X _) _) (pow_mem (ph_DlO_mem X _) _)) hj
  rw [Finset.prod_mul_distrib,
    ph_prod_tops X.Fr X.hV hr (fun s => X.DsO (s.val : ℤ) ^ (X.m1 c' - c')),
    ph_prod_shift X.Fr.J X.hV.1 (fun j => X.DlO j ^ (X.m2 c' - c')) (fun j => by
      show X.DlO (j + X.Fr.J) ^ _ = _
      rw [ph_DlO_period])] at he
  refine ⟨MvPolynomial.map (algebraMap O (KK O))
      ((∏ j ∈ Finset.range X.Fr.J, X.DlO (j : ℤ) ^ (c' * (alphaMax p X.Fr (r + K) - alpha p X.Fr (r + K) (j : ℤ)))) * H0),
    MvPolynomial.map (algebraMap O (KK O)) Y0,
    bc_IT_of_supp X.Fr _ (mul_mem (prod_mem fun j _ => pow_mem (ph_DlO_mem X _) _) hH0), inWj_map _, ?_⟩
  rw [he]
  simp only [map_add, map_mul, map_prod, map_pow, ph_DsO_map, ph_DlO_map]
  have E1 : ∏ s ∈ X.Fr.TT, X.sb (Dtop p n' O X.Fr X.hH.2.2.1 X.g (s.val : ℤ)) ^ (X.m1 c' - c') =
      X.sb (DtopProd p n' O X.Fr X.hH.2.2.1 X.g ((2 * X.Q + 3) * c')) * X.DkQ := by
    unfold Ctx.DkQ DtopProd
    rw [map_prod, map_prod, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun s _ => ?_
    rw [map_pow, map_pow, ← pow_add]
    congr 1
    unfold Ctx.m1
    omega
  have E2 : ∏ j ∈ Finset.range X.Fr.J, X.sb (Del p n' O X.Fr X.g (j : ℤ)) ^ (X.m2 c' - c') =
      (X.sb (R0 p n' O X.Fr X.g)) ^ c' * (∏ j ∈ Finset.range X.Fr.J, (X.sb (Del p n' O X.Fr X.g j)) ^ c') *
        ∏ j ∈ Finset.range X.Fr.J, X.sb (Del p n' O X.Fr X.g (j : ℤ)) ^
          (c' * (alphaMax p X.Fr (r + K) - alpha p X.Fr (r + K) (j : ℤ))) := by
    unfold R0
    rw [map_prod, ← Finset.prod_pow, ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun j hj => ?_
    rw [map_pow, ← pow_mul, ← pow_add, ← pow_add]
    congr 1
    have hle : alpha p X.Fr (r + K) (j : ℤ) ≤ alphaMax p X.Fr (r + K) :=
      Finset.le_sup (f := fun j : ℕ => alpha p X.Fr (r + K) (j : ℤ)) hj
    obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le hle
    unfold Ctx.m2
    rw [hd, Nat.add_sub_cancel_left, Nat.mul_add, Nat.mul_comm c' (alpha p X.Fr (r + K) (j : ℤ))]
    omega
  have E3 : (MvPolynomial.map (algebraMap O (KK O))) (p : MvPolynomial (TV n' (r + K)) O) ^ c' =
      C (algebraMap O (KK O) (p : O)) ^ c' := by
    simp
  rw [E1, E2, E3]
  unfold Ctx.fixedSymbolFactor
  ring

end Formalism.MainNotions.G.symbolGeneratorData
