import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.FrobeniusHodgeTateLaws.ThickFrames

open UpperTheory.V.Z.Kato.Joint

private noncomputable def avg {l : ℕ} [Fact l.Prime] (ι : PadicAlgCl l ≃+* ℂ) (N : ℕ) [NeZero N] (θ : DirichletCharacter ℂ N) (m k : ℕ)
    (ψ : DirichletCharacter (PadicAlgCl l) (l ^ m)) (δ : ℕ → PadicAlgCl l) (a b : ℤ) : ℕ → PadicAlgCl l :=
  fun i => ∑ u : (ZMod N)ˣ, δ (u : ZMod N).val * ser ι N θ m k ψ (((u : ZMod N).val : ℤ) * a) (((u : ZMod N).val : ℤ) * b) i

private theorem expand {l : ℕ} [Fact l.Prime] (ι : PadicAlgCl l ≃+* ℂ) (N : ℕ) [NeZero N] (θ : DirichletCharacter ℂ N) (m k : ℕ)
    (ψ : DirichletCharacter (PadicAlgCl l) (l ^ m)) (δ : ℕ → PadicAlgCl l) (c d : ℤ) :
    (GlobalTheory.KummerEisensteinGalois.up (l ^ m) fun i => ∑ x : ZMod N, ι.symm (GlobalTheory.EisM.hat θ (x.val : ℤ) / 2) *
                 GlobalTheory.LambdaValuationPowers.chiProj N l m k ψ δ c d (x.val : ℤ) i) =
      ((c : PadicAlgCl l) ^ 2 * (d : PadicAlgCl l) ^ 2) • avg ι N θ m k ψ δ 1 1
      - ((c : PadicAlgCl l) ^ ((3 : ℤ) - k) * ψ⁻¹ (c : ZMod (l ^ m)) * (d : PadicAlgCl l) ^ 2) • avg ι N θ m k ψ δ c 1
      - ((c : PadicAlgCl l) ^ 2 * (d : PadicAlgCl l) * ψ⁻¹ (d : ZMod (l ^ m))) • avg ι N θ m k ψ δ 1 d
      + ((c : PadicAlgCl l) ^ ((3 : ℤ) - k) * ψ⁻¹ (c : ZMod (l ^ m)) * (d : PadicAlgCl l) * ψ⁻¹ (d : ZMod (l ^ m))) •
          avg ι N θ m k ψ δ c d := by
  funext i
  simp only [GlobalTheory.KummerEisensteinGalois.up, avg, ser, GlobalTheory.LambdaValuationPowers.chiProj, GlobalTheory.LambdaValuationPowers.coPtSb, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul,
    Finset.mul_sum, mul_one]
  rw [Finset.sum_comm]
  simp only [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun x _ => ?_
  rw [show c * ((x.val : ℤ) * ((u : ZMod N).val : ℤ)) = (x.val : ℤ) * (((u : ZMod N).val : ℤ) * c) by ring,
    mul_comm d ((u : ZMod N).val : ℤ)]
  ring

private theorem sum_units {K : Type} [Field K] (n : ℕ) [NeZero n] (ψ : DirichletCharacter K n) (f : ZMod n → K) :
    ∑ a : ZMod n, ψ a * f a = ∑ b : (ZMod n)ˣ, ψ b * f b := by
  classical
  symm
  refine Finset.sum_bij_ne_zero (fun b _ _ => (b : ZMod n)) (fun _ _ _ => Finset.mem_univ _)
    (fun a _ _ b _ _ h => Units.ext h) (fun a _ h => ?_) (fun _ _ _ => rfl)
  have ha : IsUnit a := by
    by_contra hn
    exact h (by rw [MulChar.map_nonunit _ hn, zero_mul])
  obtain ⟨b, rfl⟩ := ha
  exact ⟨b, Finset.mem_univ _, h, rfl⟩

private theorem cop_unit (N : ℕ) [NeZero N] (u : (ZMod N)ˣ) (a : ℤ) (ha : IsCoprime a N) :
    IsCoprime (((u : ZMod N).val : ℤ) * a) N :=
  (Nat.isCoprime_iff_coprime.2 (ZMod.val_coe_unit_coprime u)).mul_left ha

theorem UpperTheory.V.Z.Kato.Joint.rhsEq :
    UpperTheory.V.Z.Kato.Joint.RhsEq := by
  intro hE hM l _ ι e N _ θ χ t α B cc c d δ lam κ' κ v hl he hlN hχ hα hc hd hEig hδ hlam m hm ψ z
  have hk3 : 3 ≤ 2 * e + 1 := by omega
  have hodd : Odd (2 * e + 1) := ⟨e, rfl⟩
  have hc' : IsCoprime (c : ℤ) N := Nat.isCoprime_iff_coprime.2 hc
  have hd' : IsCoprime (d : ℤ) N := Nat.isCoprime_iff_coprime.2 hd
  have h1 : IsCoprime (1 : ℤ) N := isCoprime_one_left
  unfold rhs5
  rw [expand ι N θ m (2 * e + 1) ψ δ c d]
  split_ifs with hpar
  · have hpar' : ι (ψ (-1)) = θ (-1) := by rw [hpar, RingEquiv.apply_symm_apply]
    have hf : ∀ y : ZMod (l ^ m), ι (ψ (-y)) = θ (-1) * ι (ψ y) := fun y => by
      rw [← hpar', ← map_mul, ← map_mul, neg_one_mul]
    obtain ⟨hMF, hval⟩ := hM (2 * e + 1) l N m θ χ (fun y => ι (ψ y)) t α B cc Fact.out hk3 hodd (NeZero.pos N) hlN hm hχ hf hα hEig
    set F := frm l N m (2 * e + 1) θ (θ * χ) (fun y => ι (ψ y)) with hF
    set μ := GlobalTheory.EisM.mesMu (2 * e + 1) l (GlobalTheory.EisM.hat θ) (GlobalTheory.EisM.tw2 N (θ (-1))) α B cc m (fun y => ι (ψ y)) with hμ
    have hG : (fun i => ι ((fun i => ι.symm (F i)) i)) = F := by
      funext i; simp
    have hlG : 2 * lam (fun i => ι.symm (F i)) = κ' * (N.totient : PadicAlgCl l) * ι.symm α ^ m * ι.symm μ := by
      have h2 := congrArg ι.symm hval
      rw [map_mul, map_mul, map_mul, map_pow, map_natCast, map_ofNat] at h2
      rw [hlam _ (by rw [hG]; exact hMF), hG]
      linear_combination κ' * h2
    have hav : ∀ a b : ℤ, IsCoprime a N → IsCoprime b N → lam (avg ι N θ m (2 * e + 1) ψ δ a b) =
        ι.symm (θ (a : ZMod N)) * ι.symm ((θ * χ)⁻¹ (b : ZMod N)) *
          (κ' * (N.totient : PadicAlgCl l) * ι.symm α ^ m * ι.symm μ) := by
      intro a b ha hb
      have h3 := (hE l ι N θ χ m (2 * e + 1) ψ a b hl hm hk3 hodd hχ ha hb).2.2 hpar'
      have : avg ι N θ m (2 * e + 1) ψ δ a b =
          (2 * ι.symm (θ (a : ZMod N)) * ι.symm ((θ * χ)⁻¹ (b : ZMod N))) • fun i => ι.symm (F i) := by
        funext i
        apply ι.injective
        simp only [avg, Pi.smul_apply, smul_eq_mul, map_mul, map_sum, RingEquiv.apply_symm_apply, map_ofNat]
        rw [← h3 i]
        refine Finset.sum_congr rfl fun u _ => ?_
        rw [hδ _ (ZMod.val_coe_unit_coprime u), ZMod.natCast_zmod_val]
      rw [this, map_smul, smul_eq_mul, ← hlG]
      ring
    haveI : NeZero (l ^ m) := ⟨pow_ne_zero _ (Fact.out : l.Prime).ne_zero⟩
    rw [sum_units (l ^ m) ψ (fun a => z ^ a.val)]
    simp only [map_add, map_sub, map_smul, smul_eq_mul, hav _ _ h1 h1, hav _ _ hc' h1, hav _ _ h1 hd', hav _ _ hc' hd',
      Fin.sum_univ_four, smB, smT, Int.cast_natCast, Int.cast_one, map_one]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons,
      Matrix.tail_cons, Nat.cast_mul, map_mul]
    ring
  · have hpar' : ι (ψ (-1)) ≠ θ (-1) := fun h => hpar (by rw [← h, RingEquiv.symm_apply_apply])
    have hav : ∀ a b : ℤ, IsCoprime a N → IsCoprime b N → avg ι N θ m (2 * e + 1) ψ δ a b = 0 := by
      intro a b ha hb
      funext i
      refine Finset.sum_eq_zero fun u _ => ?_
      rw [(hE l ι N θ χ m (2 * e + 1) ψ _ _ hl hm hk3 hodd hχ (cop_unit N u a ha) (cop_unit N u b hb)).1 hpar']
      simp
    rw [hav _ _ h1 h1, hav _ _ hc' h1, hav _ _ h1 hd', hav _ _ hc' hd']
    simp
