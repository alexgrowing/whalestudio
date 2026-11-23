import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.SignatureIntegrality.SignatureTorusFixedPoints.FactJ
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.SignatureIntegrality.SignatureTorusFixedPoints.Shrink
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.SignatureIntegrality.SignatureTorusFixedPoints.IsOpenKc
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.SignatureIntegrality.HodgeTateFromSandwich

noncomputable section

open ValuativeRel Matrix Polynomial GlobalTheory.SmGL GlobalTheory.SplitWeil UpperTheory.V.Hi UpperTheory.V.AlgebraTools UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Sig UpperTheory.V.Z.Sym.Loc UpperTheory.V.Z.Sym.Glob

private theorem quot0 {R : Type} [CommRing R] (I : Ideal R) (u v : R ⧸ I ^ 0) : u = v := by
  haveI : Subsingleton (R ⧸ I ^ 0) := Ideal.Quotient.subsingleton_iff.mpr (by simp)
  exact Subsingleton.elim u v

private theorem mem_kc_zero_of_mem_ko {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] {n : ℕ} (x : GL (Fin n) k) (hx : x ∈ KO k (Fin n)) :
    x ∈ Kc k n 0 := by
  obtain ⟨x0, rfl⟩ := hx
  refine ⟨x0, MonoidHom.mem_ker.2 ?_, rfl⟩
  exact Units.ext (Matrix.ext fun i j => quot0 _ _ _)

private theorem conj_mem_kc_of_mem_ko {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] {n : ℕ} (m : ℕ) (t x : GL (Fin n) k) (ht : t ∈ KO k (Fin n))
    (hx : x ∈ Kc k n m) : t * x * t⁻¹ ∈ Kc k n m := by
  obtain ⟨t0, rfl⟩ := ht
  obtain ⟨x0, hx0, rfl⟩ := hx
  exact ⟨t0 * x0 * t0⁻¹, (MonoidHom.normal_ker _).conj_mem x0 hx0 t0, by simp [map_mul, map_inv]⟩

private theorem mem_ko_and_torus_of_mem_th {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] {n : ℕ} (V : Lev k) (t : GL (Fin n) k) (ht : t ∈ V.TH n) :
    t ∈ KO k (Fin n) ∧ t ∈ (glIwa k n).T := by
  obtain ⟨d, hd, rfl⟩ := ht
  have hv : ∀ i, valuation k (d i : k) = 1 := fun i => V.H_le (hd i (Set.mem_univ i))
  refine ⟨?_, ⟨d, fun i => hv i, rfl⟩⟩
  have hO : ∀ i, (d i : k) ∈ 𝒪[k] := fun i => (Valuation.mem_integer_iff _ _).2 (hv i).le
  let d0 : Fin n → (𝒪[k])ˣ := fun i =>
    ((Valuation.integer.integers (valuation k)).isUnit_of_one' (x := ⟨d i, hO i⟩) (hv i)).unit
  refine ⟨diagT (𝒪[k]) (Fin n) d0, ?_⟩
  ext i j
  simp [diagT, leviEmb, leviTorus, Matrix.diagonal_apply]
  split_ifs <;> simp [d0] <;> rfl

private theorem map_mem_j_of_pres {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] {n : ℕ} (V : Lev k) (σ : GL (Fin n) k →* GL (Fin n) k)
    (hσ : Pres V σ) (g : GL (Fin n) k) (hg : g ∈ V.J n) : σ g ∈ V.J n := by
  unfold Lev.J at hg ⊢
  have h : (glIwa k n).N ⊔ V.TH n ⊔ (glIwa k n).Nm V.c ≤
      ((glIwa k n).N ⊔ V.TH n ⊔ (glIwa k n).Nm V.c).comap σ := by
    refine sup_le (sup_le ?_ ?_) ?_ <;> intro x hx <;> rw [Subgroup.mem_comap]
    · exact Subgroup.mem_sup_left (Subgroup.mem_sup_left (hσ.N x hx))
    · exact Subgroup.mem_sup_left (Subgroup.mem_sup_right (hσ.T x hx))
    · exact Subgroup.mem_sup_right (hσ.Nm V.c x hx)
  exact h hg

theorem UpperTheory.V.Z.Sym.Sig.contract : UpperTheory.V.Z.Sym.Sig.Contract := by
  intro k _ _ _ _ V n σ hσ d hd g hg
  obtain ⟨x, hx, y, hy, rfl⟩ := hg
  have NJ : ∀ z ∈ (glIwa k n).N, z ∈ V.J n := fun z hz =>
    Subgroup.mem_sup_left (Subgroup.mem_sup_left hz)
  have NmJ : ∀ z ∈ (glIwa k n).Nm V.c, z ∈ V.J n := fun z hz => Subgroup.mem_sup_right hz
  have NKO : ∀ z ∈ (glIwa k n).N, z ∈ KO k (Fin n) := fun z hz => hz.2
  have NmKO : ∀ c, ∀ z ∈ (glIwa k n).Nm c, z ∈ KO k (Fin n) := fun c z hz =>
    Subgroup.map_le_range _ _ hz.2
  have hh : y * σ x ∈ V.J n := mul_mem hy (map_mem_j_of_pres V σ hσ x hx)
  have key : ∀ u : (glIwa k n).N, ∃ a ∈ (glIwa k n).N, ∃ s ∈ V.TH n, ∃ b ∈ (glIwa k n).Nm V.c,
      y * σ x * σ (u : GL (Fin n) k) = a * s * b := fun u =>
    (factJ k V n).1 _ (mul_mem hh (NJ _ (hσ.N _ u.2)))
  choose a ha s hs b hb hab using key
  let Ψ : (glIwa k n).N → (glIwa k n).N := fun u =>
    ⟨dg d * a u * (dg d)⁻¹,
      ((shrink k n d hd 0).1 (a u) (ha u) (mem_kc_zero_of_mem_ko _ (NKO _ (ha u)))).1⟩
  obtain ⟨u, hu⟩ := fixPt k n (glIwa k n).N (Or.inl rfl) Ψ (by
    intro m u1 u2 h12
    have e1 : (y * σ x * σ (u1 : GL (Fin n) k))⁻¹ * (y * σ x * σ (u2 : GL (Fin n) k)) =
        σ ((u1 : GL (Fin n) k)⁻¹ * u2) := by
      rw [map_mul, map_inv]
      group
    have h1 : (a u1 * s u1 * b u1)⁻¹ * (a u2 * s u2 * b u2) ∈ Kc k n m := by
      rw [← hab, ← hab, e1]
      exact hσ.K m _ h12
    have h2 := (factJ k V n).2 m _ (ha u1) _ (ha u2) _ (hs u1) _ (hs u2) _ (hb u1) _ (hb u2) h1
    have h3 := ((shrink k n d hd m).1 _ (mul_mem (inv_mem (ha u1)) (ha u2)) h2).2
    have e2 : ((Ψ u1 : GL (Fin n) k))⁻¹ * (Ψ u2 : GL (Fin n) k) =
        dg d * ((a u1)⁻¹ * a u2) * (dg d)⁻¹ := by
      simp only [Ψ]
      group
    rw [e2]
    exact h3)
  have hu' : dg d * a u * (dg d)⁻¹ = (u : GL (Fin n) k) := congrArg Subtype.val hu
  have ht := mem_ko_and_torus_of_mem_th V _ (hs u)
  have tinvT : (s u)⁻¹ ∈ (glIwa k n).T := inv_mem ht.2
  have memΨ : ∀ w ∈ (glIwa k n).Nm V.c,
      (b u)⁻¹ * ((s u)⁻¹ * ((dg d)⁻¹ * σ w * dg d) * s u) ∈ (glIwa k n).Nm V.c := by
    intro w hw
    refine mul_mem (inv_mem (hb u)) ?_
    have h1 := ((shrink k n d hd 0).2 V.c (σ w) (hσ.Nm _ _ hw)
      (mem_kc_zero_of_mem_ko _ (NmKO _ _ (hσ.Nm _ _ hw)))).1
    have h2 := (glIwa k n).T_Nm V.c _ tinvT _ h1
    rwa [inv_inv] at h2
  let Ψ₂ : (glIwa k n).Nm V.c → (glIwa k n).Nm V.c := fun w => ⟨_, memΨ w w.2⟩
  obtain ⟨w, hw⟩ := fixPt k n ((glIwa k n).Nm V.c) (Or.inr ⟨V.c, rfl⟩) Ψ₂ (by
    intro m w1 w2 h12
    have e : ((Ψ₂ w1 : GL (Fin n) k))⁻¹ * (Ψ₂ w2 : GL (Fin n) k) =
        (s u)⁻¹ * ((dg d)⁻¹ * σ ((w1 : GL (Fin n) k)⁻¹ * w2) * dg d) * ((s u)⁻¹)⁻¹ := by
      simp only [Ψ₂]
      rw [map_mul, map_inv]
      group
    rw [e]
    refine conj_mem_kc_of_mem_ko _ _ _ (inv_mem ht.1) ?_
    have hmem : σ ((w1 : GL (Fin n) k)⁻¹ * w2) ∈ (glIwa k n).Nm V.c :=
      hσ.Nm _ _ (mul_mem (inv_mem w1.2) w2.2)
    exact ((shrink k n d hd m).2 V.c _ hmem (hσ.K m _ h12)).2)
  have hw' : (b u)⁻¹ * ((s u)⁻¹ * ((dg d)⁻¹ * σ w * dg d) * s u) = (w : GL (Fin n) k) :=
    congrArg Subtype.val hw
  have comm : dg d * s u = s u * dg d :=
    (glIwa k n).comm _ ⟨d, rfl⟩ _ ((glIwa k n).T_le ht.2)
  refine ⟨x * u * σ w, mul_mem (mul_mem hx (NJ _ u.2)) (NmJ _ (hσ.Nm _ _ w.2)), s u, hs u, ?_⟩
  rw [map_mul, map_mul, hσ.invol]
  have E0 : (x * (u : GL (Fin n) k) * σ w)⁻¹ * (x * dg d * y) * (σ x * σ (u : GL (Fin n) k) * w) =
      (σ w)⁻¹ * ((u : GL (Fin n) k)⁻¹ * dg d * (y * σ x * σ (u : GL (Fin n) k)) * w) := by
    group
  have E4 : b u * (w : GL (Fin n) k) = (s u)⁻¹ * ((dg d)⁻¹ * σ w * dg d) * s u := by
    conv_lhs => rw [← hw']
    group
  rw [E0, hab u, ← hu']
  have E5 : (dg d * a u * (dg d)⁻¹)⁻¹ * dg d * (a u * s u * b u) * (w : GL (Fin n) k) =
      dg d * s u * (b u * w) := by
    group
  rw [E5, E4, ← comm]
  group

end
